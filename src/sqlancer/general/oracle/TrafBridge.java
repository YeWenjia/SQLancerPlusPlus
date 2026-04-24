package sqlancer.general.oracle;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;

import org.json.JSONArray;
import org.json.JSONObject;

/**
 * Java-side wrapper around traf's sqlancer_bridge Python worker. One instance owns a single Python
 * subprocess; create one per SQLancer++ thread. Not thread-safe.
 */
public final class TrafBridge implements AutoCloseable {

    private final Process process;
    private final BufferedWriter stdin;
    private final BufferedReader stdout;

    public TrafBridge(Path trafRepo) throws IOException {
        ProcessBuilder pb = new ProcessBuilder("python", "-u", "-m", "interpreter.sqlancer_bridge");
        pb.directory(trafRepo.toFile());
        pb.redirectErrorStream(false);
        this.process = pb.start();
        this.stdin = new BufferedWriter(new OutputStreamWriter(process.getOutputStream(), StandardCharsets.UTF_8));
        this.stdout = new BufferedReader(new InputStreamReader(process.getInputStream(), StandardCharsets.UTF_8));
        // Discard stderr to avoid backpressure deadlocks.
        Thread drain = new Thread(() -> {
            try (BufferedReader err = new BufferedReader(
                    new InputStreamReader(process.getErrorStream(), StandardCharsets.UTF_8))) {
                String l;
                while ((l = err.readLine()) != null) {
                    // Forward to stderr for debugging.
                    System.err.println("[traf] " + l);
                }
            } catch (IOException ignored) {
                // process died
            }
        }, "traf-bridge-stderr");
        drain.setDaemon(true);
        drain.start();
        // Probe the worker so construction surfaces setup errors early.
        JSONObject resp = call(new JSONObject().put("op", "ping"));
        if (!resp.optBoolean("ok")) {
            throw new IOException("traf bridge ping failed: " + resp);
        }
    }

    /**
     * Locate the traf-prototype repo. Checked, in order:
     * <ol>
     *   <li>{@code TRAF_REPO} env var / {@code traf.repo} system property (explicit override)</li>
     *   <li>{@code ./traf-prototype/} — traf is a sibling submodule under the CWD</li>
     *   <li>{@code ../} — SQLancer++ is itself a submodule inside traf-prototype</li>
     *   <li>{@code .} — CWD is already the traf-prototype root</li>
     * </ol>
     * A directory qualifies if it contains {@code interpreter/sqlancer_bridge.py}.
     */
    public static Path defaultTrafRepo() {
        String override = System.getProperty("traf.repo", System.getenv("TRAF_REPO"));
        if (override != null && !override.isEmpty()) {
            Path p = Paths.get(override).toAbsolutePath();
            if (looksLikeTraf(p)) {
                return p;
            }
            throw new IllegalStateException("TRAF_REPO=" + p + " is not a traf-prototype checkout");
        }
        Path[] candidates = { Paths.get("traf-prototype"), Paths.get(".."), Paths.get(".") };
        for (Path c : candidates) {
            Path abs = c.toAbsolutePath().normalize();
            if (looksLikeTraf(abs)) {
                return abs;
            }
        }
        throw new IllegalStateException(
                "Cannot find traf-prototype (looked for ./traf-prototype, .., .). Set TRAF_REPO.");
    }

    private static boolean looksLikeTraf(Path p) {
        return Files.isDirectory(p) && Files.isRegularFile(p.resolve("interpreter/sqlancer_bridge.py"));
    }

    private synchronized JSONObject call(JSONObject req) throws IOException {
        stdin.write(req.toString());
        stdin.write('\n');
        stdin.flush();
        String line = stdout.readLine();
        if (line == null) {
            throw new IOException("traf bridge closed stdout");
        }
        return new JSONObject(line);
    }

    public void setSchema(String engine, JSONObject tables, JSONObject data) throws IOException {
        JSONObject req = new JSONObject().put("op", "set_schema").put("engine", engine).put("tables", tables)
                .put("data", data);
        JSONObject resp = call(req);
        if (!resp.optBoolean("ok")) {
            throw new IOException("traf set_schema failed: " + resp.optString("error"));
        }
    }

    public static final class CheckResult {
        public final boolean ok;
        public final String stage;
        public final String error;

        CheckResult(boolean ok, String stage, String error) {
            this.ok = ok;
            this.stage = stage;
            this.error = error;
        }
    }

    public CheckResult check(String sql) throws IOException {
        JSONObject resp = call(new JSONObject().put("op", "check").put("sql", sql));
        return new CheckResult(resp.optBoolean("ok"), resp.optString("stage", ""), resp.optString("error", ""));
    }

    public static final class RunResult {
        public final boolean ok;
        public final List<String> cols;
        public final JSONArray rows;
        public final String error;
        public final String trace;

        RunResult(boolean ok, List<String> cols, JSONArray rows, String error, String trace) {
            this.ok = ok;
            this.cols = cols;
            this.rows = rows;
            this.error = error;
            this.trace = trace;
        }
    }

    public RunResult run(String sql) throws IOException {
        JSONObject resp = call(new JSONObject().put("op", "run").put("sql", sql));
        boolean ok = resp.optBoolean("ok");
        if (!ok) {
            return new RunResult(false, null, null, resp.optString("error", ""), resp.optString("trace", ""));
        }
        JSONArray colsJson = resp.optJSONArray("cols");
        java.util.ArrayList<String> cols = new java.util.ArrayList<>();
        if (colsJson != null) {
            for (int i = 0; i < colsJson.length(); i++) {
                cols.add(colsJson.getString(i));
            }
        }
        return new RunResult(true, cols, resp.optJSONArray("rows"), "", "");
    }

    @Override
    public void close() {
        try {
            stdin.write(new JSONObject().put("op", "shutdown").toString());
            stdin.write('\n');
            stdin.flush();
        } catch (IOException ignored) {
            // process may already be dead
        }
        try {
            process.waitFor();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            process.destroy();
        }
    }
}
