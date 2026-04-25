package sqlancer.general.oracle;

import java.io.IOException;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.sql.ResultSet;
import java.sql.ResultSetMetaData;
import java.sql.SQLException;
import java.sql.Statement;
import java.sql.Types;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.json.JSONArray;
import org.json.JSONObject;

import sqlancer.IgnoreMeException;
import sqlancer.Main;
import sqlancer.Randomly;
import sqlancer.Reproducer;
// import sqlancer.common.query.Query;
// import sqlancer.common.query.SQLQueryAdapter;
import sqlancer.common.ast.newast.ColumnReferenceNode;
import sqlancer.common.ast.newast.Node;
import sqlancer.common.ast.newast.TableReferenceNode;
import sqlancer.common.gen.ExpressionGenerator;
import sqlancer.common.oracle.TestOracle;
import sqlancer.general.GeneralErrorHandler.GeneratorNode;
import sqlancer.general.GeneralProvider.GeneralGlobalState;
import sqlancer.general.GeneralSchema;
import sqlancer.general.GeneralSchema.GeneralColumn;
import sqlancer.general.GeneralSchema.GeneralDataType;
import sqlancer.general.GeneralSchema.GeneralTable;
import sqlancer.general.GeneralSchema.GeneralTables;
import sqlancer.general.GeneralToStringVisitor;
import sqlancer.general.ast.GeneralExpression;
import sqlancer.general.ast.GeneralJoin;
import sqlancer.general.ast.GeneralSelect;
import sqlancer.general.gen.GeneralRandomQuerySynthesizer;

/**
 * Differential oracle that uses traf as a reference interpreter.
 *
 * For each generated SELECT:
 *   1. Ask traf to parse+typecheck — skip if traf doesn't support the query.
 *   2. Execute on the real DBMS via JDBC; capture rows.
 *   3. Execute on traf; capture rows.
 *   4. If results match, emit a YAML test-suite entry.
 *   5. If traf crashes or results disagree, raise an AssertionError so SQLancer++ logs it.
 *
 * Suite output mirrors the YAML-per-folder shape used by traf/test/spider.
 */
public class GeneralTrafTestSuiteOracle implements TestOracle<GeneralGlobalState> {

    /**
     * Per-database accepted-case budget. Non-static on purpose: the oracle is instantiated once
     * per database iteration (see ProviderAdapter.generateAndTestDatabase), so this counter
     * naturally resets whenever SQLancer++ rotates to a fresh database. With suiteSize=100 and
     * enough --num-queries, each database contributes up to 100 accepted cases to the suite.
     */
    private final AtomicInteger acceptedCount = new AtomicInteger(0);
    /**
     * Per-category filename index. Stays static so files within a category don't collide across
     * databases or threads. Each category gets its own counter so numbering is contiguous per
     * folder.
     */
    private static final ConcurrentHashMap<String, AtomicInteger> CATEGORY_INDEX = new ConcurrentHashMap<>();

    private static final String CAT_BENIGN = "benign";
    private static final String CAT_MISMATCH = "traf-mismatch";
    private static final String CAT_TRAF_CRASH = "traf-crash";
    private static final String CAT_DBMS_FAIL = "dbms-fail";
    private static final String CAT_BOTH_FAIL = "both-fail";

    /** Per-(parent,engine) guard so we wipe stale case folders only once per JVM run. */
    private static final ConcurrentHashMap<String, AtomicBoolean> CLEANED = new ConcurrentHashMap<>();

    /**
     * Per-thread bridge cache. The oracle is re-created every iteration, but starting a fresh
     * Python worker per iteration leaks processes and burns ~200 ms of import cost each time.
     * Keyed by thread id so multi-threaded runs each get their own (the Python worker holds
     * per-thread schema state that can't be shared).
     */
    private static final ConcurrentHashMap<Long, TrafBridge> BRIDGES = new ConcurrentHashMap<>();
    static {
        Runtime.getRuntime().addShutdownHook(new Thread(() -> {
            BRIDGES.values().forEach(b -> {
                try {
                    b.close();
                } catch (RuntimeException ignored) {
                    // best-effort teardown
                }
            });
        }, "traf-bridge-shutdown"));
    }

    private final GeneralGlobalState state;
    private final String trafEngine;
    private final Path outputDir;
    private final int suiteSize;
    private int lastSchemaVersion = -1;
    private JSONObject currentSchemaTables = new JSONObject();
    private JSONObject currentSchemaData = new JSONObject();
    private Reproducer<GeneralGlobalState> reproducer;

    public GeneralTrafTestSuiteOracle(GeneralGlobalState state) {
        this.state = state;
        sqlancer.general.GeneralOptions opts = state.getDbmsSpecificOptions();
        this.trafEngine = mapEngine(opts.getDatabaseEngineFactory().name());
        this.outputDir = Paths.get(opts.trafSuiteOutput).toAbsolutePath();
        this.suiteSize = opts.trafSuiteSize;
        try {
            Files.createDirectories(outputDir);
        } catch (IOException e) {
            throw new RuntimeException("Cannot create suite output dir " + outputDir, e);
        }
        cleanCategoryDirsOnce();
    }

    /**
     * Wipe all <engine>-* case folders under the suite parent at startup, so each run begins
     * with a clean slate and case_NNNNNN.yml numbering matches what's on disk.
     */
    private void cleanCategoryDirsOnce() {
        Path parent = outputDir.getParent();
        if (parent == null) {
            parent = outputDir;
        }
        String key = parent.toString() + "::" + trafEngine;
        AtomicBoolean flag = CLEANED.computeIfAbsent(key, k -> new AtomicBoolean(false));
        if (!flag.compareAndSet(false, true)) {
            return;
        }
        String prefix = trafEngine + "-";
        if (!Files.isDirectory(parent)) {
            return;
        }
        try (Stream<Path> entries = Files.list(parent)) {
            entries.filter(Files::isDirectory)
                    .filter(p -> p.getFileName().toString().startsWith(prefix))
                    .forEach(GeneralTrafTestSuiteOracle::deleteRecursively);
        } catch (IOException e) {
            System.err.println("traf suite cleanup failed for " + parent + ": " + e);
        }
    }

    private static void deleteRecursively(Path root) {
        try (Stream<Path> walk = Files.walk(root)) {
            walk.sorted(Comparator.reverseOrder()).forEach(p -> {
                try {
                    Files.deleteIfExists(p);
                } catch (IOException ignored) {
                }
            });
        } catch (IOException e) {
            System.err.println("traf suite cleanup failed for " + root + ": " + e);
        }
    }

    private TrafBridge bridge() {
        return BRIDGES.computeIfAbsent(Thread.currentThread().getId(), id -> {
            try {
                return new TrafBridge(TrafBridge.defaultTrafRepo());
            } catch (IOException e) {
                throw new RuntimeException("Failed to start traf bridge", e);
            }
        });
    }

    private static String mapEngine(String dbms) {
        switch (dbms.toUpperCase()) {
        case "SQLITE":
            return "sqlite";
        case "POSTGRESQL":
        case "POSTGRES":
            return "postgres";
        case "MYSQL":
        case "MARIADB":
            return "mysql";
        default:
            // Fall back to sqlite semantics; traf doesn't model every DBMS.
            return "sqlite";
        }
    }

    @Override
    public void check() throws SQLException {
        reproducer = null;

        if (acceptedCount.get() >= suiteSize) {
            // Per-database suite target reached; skip remaining check() calls for this database.
            // A fresh oracle (and thus a fresh counter) will be built for the next database.
            throw new IgnoreMeException();
        }

        pushSchemaIfChanged();

        // Generate a SELECT using the same plumbing as the fuzzing oracle.
        GeneralSchema schema = state.getSchema();
        GeneralTables targetTables = schema.getRandomTableNonEmptyTables();
        List<GeneralColumn> columns = targetTables.getColumns();

        ExpressionGenerator<Node<GeneralExpression>> gen = GeneralRandomQuerySynthesizer.getExpressionGenerator(state,
                columns);
        Node<GeneralExpression> whereClause = gen.generateExpression();

        List<GeneralTable> tables = targetTables.getTables();
        List<TableReferenceNode<GeneralExpression, GeneralTable>> tableList = tables.stream()
                .map(t -> new TableReferenceNode<GeneralExpression, GeneralTable>(t)).collect(Collectors.toList());
        List<Node<GeneralExpression>> joins;
        if (Randomly.getBoolean() || !state.getHandler().getOption(GeneratorNode.SUBQUERY)) {
            joins = GeneralJoin.getJoins(tableList, state);
        } else {
            joins = GeneralJoin.getJoinsWithSubquery(tableList, state);
        }

        GeneralSelect select = new GeneralSelect();
        List<Node<GeneralExpression>> fetchColumns = new ArrayList<>();
        if (Randomly.getBoolean()) {
            fetchColumns.add(new ColumnReferenceNode<>(new GeneralColumn("*", null, false, false)));
        } else {
            fetchColumns = Randomly.nonEmptySubset(columns).stream()
                    .map(c -> new ColumnReferenceNode<GeneralExpression, GeneralColumn>(c))
                    .collect(Collectors.toList());
        }
        select.setFetchColumns(fetchColumns);
        select.setFromList(tableList.stream().collect(Collectors.toList()));
        select.setJoinList(joins.stream().collect(Collectors.toList()));
        select.setWhereClause(whereClause);

        String sql = GeneralToStringVisitor.asString(select);
        state.getState().getLocalState().log(sql);

        // 1. Traf filter.
        TrafBridge.CheckResult ck;
        try {
            ck = bridge().check(sql);
        } catch (IOException e) {
            throw new RuntimeException("traf bridge error", e);
        }
        if (!ck.ok) {
            // Unsupported feature — drop silently, not a bug.
            throw new IgnoreMeException();
        }

        // 2. Execute on real DBMS.
        List<List<Object>> dbmsRows;
        List<String> dbmsCols;
        boolean isError = false;
        String dbmsErrorMessage = null;
        try (Statement stmt = state.getConnection().createStatement()) {
            if (state.getOptions().logEachSelect()) {
                state.getLogger().writeCurrent(sql);
            }
            try (ResultSet rs = stmt.executeQuery(sql)) {
                dbmsCols = extractCols(rs);
                dbmsRows = extractRows(rs);
            }
            Main.nrSuccessfulActions.addAndGet(1);
        } catch (SQLException e) {
            Main.nrUnsuccessfulActions.addAndGet(1);
            state.getLogger().writeCurrent("-- " + e.getMessage());
            // throw new IgnoreMeException();
            isError = true;
            dbmsErrorMessage = e.getMessage();
            dbmsCols = Collections.emptyList();
            dbmsRows = Collections.emptyList();
            // throw new AssertionError("DBMS error occurred: " + dbmsErrorMessage + "\nSQL: " + sql);
        }

        // 3. Execute on traf.
        TrafBridge.RunResult trafRes;
        try {
            trafRes = bridge().run(sql);
        } catch (IOException e) {
            throw new RuntimeException("traf bridge error", e);
        }

        boolean dbmsOk = !isError;
        boolean trafOk = trafRes.ok;

        // 4. Bucket the case based on (DBMS, traf) outcome.
        if (dbmsOk && trafOk) {
            List<List<String>> dbmsNorm = normalizeRows(dbmsRows);
            List<List<String>> trafNorm = normalizeTrafRows(trafRes.rows);
            if (!bagsEqual(dbmsNorm, trafNorm)) {
                writeCase(CAT_MISMATCH, sql, dbmsCols, dbmsRows, null, trafRes.cols, trafNorm, null, null);
                String msg = "traf/DBMS result mismatch.\nSQL: " + sql + "\nDBMS cols: " + dbmsCols + "\nDBMS rows: "
                        + dbmsNorm + "\nTraf cols: " + trafRes.cols + "\nTraf rows: " + trafNorm;
                reproducer = new MismatchReproducer(msg);
                throw new AssertionError(msg);
            }
            writeCase(CAT_BENIGN, sql, dbmsCols, dbmsRows, null, trafRes.cols, normalizeTrafRows(trafRes.rows), null,
                    null);
            acceptedCount.incrementAndGet();
        } else if (dbmsOk && !trafOk) {
            // DBMS handled it; traf failed after typecheck — candidate traf bug.
            writeCase(CAT_TRAF_CRASH, sql, dbmsCols, dbmsRows, null, Collections.emptyList(), Collections.emptyList(),
                    trafRes.error, trafRes.trace);
            String msg = "traf run() failed after successful typecheck.\nSQL: " + sql + "\nError: " + trafRes.error;
            reproducer = new MismatchReproducer(msg);
            throw new AssertionError(msg);
        } else if (!dbmsOk && trafOk) {
            // DBMS rejected the query but traf accepted — collect for later analysis.
            writeCase(CAT_DBMS_FAIL, sql, Collections.emptyList(), Collections.emptyList(), dbmsErrorMessage,
                    trafRes.cols, normalizeTrafRows(trafRes.rows), null, null);
            throw new AssertionError("DBMS rejected the query but traf accepted." + "\nSQL: " + sql + "\nDBMS error: " + dbmsErrorMessage + "\nTraf cols: " + trafRes.cols
                    + "\nTraf rows: " + normalizeTrafRows(trafRes.rows));
        } else {
            // Both sides rejected the query — usually uninteresting, but kept for completeness.
            writeCase(CAT_BOTH_FAIL, sql, Collections.emptyList(), Collections.emptyList(), dbmsErrorMessage,
                    Collections.emptyList(), Collections.emptyList(), trafRes.error, trafRes.trace);
            throw new IgnoreMeException();
        }
    }

    private Path categoryDir(String category) {
        Path parent = outputDir.getParent();
        if (parent == null) {
            parent = outputDir;
        }
        return parent.resolve(trafEngine + "-" + category);
    }

    private static int nextIndex(String category) {
        return CATEGORY_INDEX.computeIfAbsent(category, k -> new AtomicInteger(0)).incrementAndGet();
    }

    /**
     * Collect DDL/DML statements that produced the current DBMS state. The SELECT under test is
     * logged into the same list just before the oracle runs, so we drop the trailing SELECT.
     *
     * SQLancer++ logs both successful and failed statements when `loggerPrintFailed=true` (the
     * default). We filter out failed ones so the emitted `setup_sql` replays cleanly.
     */
    // private List<String> collectSetupSql() {
    //     List<String> out = new ArrayList<>();
    //     List<? extends Query<?>> stmts = state.getState().getStatements();
    //     for (Query<?> q : stmts) {
    //         if (q instanceof SQLQueryAdapter && ((SQLQueryAdapter) q).getLastErrorMessage() != null) {
    //             // Statement failed at execution — don't emit it.
    //             continue;
    //         }
    //         String s = q.getQueryString();
    //         if (s == null) {
    //             continue;
    //         }
    //         s = s.trim();
    //         if (s.isEmpty()) {
    //             continue;
    //         }
    //         out.add(s);
    //     }
    //     // Drop the trailing SELECT — it's emitted separately as `sql:`.
    //     if (!out.isEmpty() && out.get(out.size() - 1).toUpperCase().startsWith("SELECT")) {
    //         out.remove(out.size() - 1);
    //     }
    //     return out;
    // }

    private void writeCase(String category, String sql, List<String> dbmsCols, List<List<Object>> dbmsRows,
            String dbmsError, List<String> trafCols, List<List<String>> trafRows, String trafError, String trafTrace) {
        Path dir = categoryDir(category);
        try {
            Files.createDirectories(dir);
        } catch (IOException ignored) {
        }
        int idx = nextIndex(category);
        Path file = dir.resolve(String.format("case_%06d.yml", idx));
        StringBuilder extra = new StringBuilder();
        extra.append("kind: ").append(category).append('\n');
        if (dbmsError != null) {
            extra.append("dbms_error: ").append(yamlScalar(dbmsError)).append('\n');
        }
        if (trafError != null) {
            extra.append("traf_error: ").append(yamlScalar(trafError)).append('\n');
        }
        if (trafTrace != null) {
            extra.append("traf_trace: ").append(yamlScalar(trafTrace)).append('\n');
        }
        if (trafCols != null) {
            extra.append("traf_columns: ").append(trafCols).append('\n');
            if (trafRows == null || trafRows.isEmpty()) {
                extra.append("traf_rows: []\n");
            } else {
                extra.append("traf_rows:\n");
                for (List<String> r : trafRows) {
                    extra.append("  - [");
                    for (int i = 0; i < r.size(); i++) {
                        if (i > 0) {
                            extra.append(", ");
                        }
                        extra.append(yamlScalar(r.get(i)));
                    }
                    extra.append("]\n");
                }
            }
        }
        writeYaml(file, sql, dbmsCols, dbmsRows, extra.toString());
    }

    private void pushSchemaIfChanged() {
        GeneralSchema schema = state.getSchema();
        int version = schema.getDatabaseTables().stream().mapToInt(t -> (t.getName() + t.getColumns().size()).hashCode())
                .sum();
        if (version == lastSchemaVersion) {
            return;
        }
        JSONObject tables = new JSONObject();
        JSONObject data = new JSONObject();
        for (GeneralTable t : schema.getDatabaseTables()) {
            if (t.isView()) {
                continue;
            }
            JSONArray cols = new JSONArray();
            for (GeneralColumn c : t.getColumns()) {
                String trafType = trafTypeFor(c.getType().getPrimitiveDataType());
                if (trafType == null) {
                    // Schema contains a type traf can't represent — drop the table from the mirror.
                    cols = null;
                    break;
                }
                cols.put(new JSONObject().put("name", c.getName()).put("type", trafType));
            }
            if (cols == null) {
                continue;
            }
            tables.put(t.getName(), cols);
            data.put(t.getName(), fetchRows(t));
        }
        try {
            bridge().setSchema(trafEngine, tables, data);
            lastSchemaVersion = version;
            currentSchemaTables = tables;
            currentSchemaData = data;
        } catch (IOException e) {
            throw new RuntimeException("traf set_schema failed", e);
        }
    }

    private static String trafTypeFor(GeneralDataType dt) {
        switch (dt) {
        case INT:
            return "int";
        case STRING:
            return "string";
        case BOOLEAN:
            // traf has no BType in its table types; skip boolean columns.
            return null;
        default:
            // VARTYPE / NULL — unknown mapping.
            return null;
        }
    }

    private JSONArray fetchRows(GeneralTable t) {
        JSONArray rows = new JSONArray();
        try (Statement s = state.getConnection().createStatement();
                ResultSet rs = s.executeQuery("SELECT * FROM " + t.getName())) {
            ResultSetMetaData md = rs.getMetaData();
            int n = md.getColumnCount();
            while (rs.next()) {
                JSONArray row = new JSONArray();
                for (int i = 1; i <= n; i++) {
                    row.put(cellToJson(rs, i, md.getColumnType(i)));
                }
                rows.put(row);
            }
        } catch (SQLException e) {
            // Table unreadable (e.g. just dropped) — mirror as empty.
        }
        return rows;
    }

    private Object cellToJson(ResultSet rs, int i, int sqlType) throws SQLException {
        Object v = rs.getObject(i);
        if (v == null || rs.wasNull()) {
            return JSONObject.NULL;
        }
        switch (sqlType) {
        case Types.INTEGER:
        case Types.BIGINT:
        case Types.SMALLINT:
        case Types.TINYINT:
            return rs.getLong(i);
        case Types.FLOAT:
        case Types.DOUBLE:
        case Types.REAL:
        case Types.DECIMAL:
        case Types.NUMERIC:
            return rs.getDouble(i);
        default:
            return v.toString();
        }
    }

    private List<String> extractCols(ResultSet rs) throws SQLException {
        ResultSetMetaData md = rs.getMetaData();
        List<String> out = new ArrayList<>();
        for (int i = 1; i <= md.getColumnCount(); i++) {
            out.add(md.getColumnLabel(i));
        }
        return out;
    }

    private List<List<Object>> extractRows(ResultSet rs) throws SQLException {
        List<List<Object>> out = new ArrayList<>();
        ResultSetMetaData md = rs.getMetaData();
        int n = md.getColumnCount();
        while (rs.next()) {
            List<Object> row = new ArrayList<>(n);
            for (int i = 1; i <= n; i++) {
                Object v = rs.getObject(i);
                if (rs.wasNull()) {
                    v = null;
                }
                row.add(v);
            }
            out.add(row);
        }
        return out;
    }

    private List<List<String>> normalizeRows(List<List<Object>> rows) {
        List<List<String>> out = new ArrayList<>();
        for (List<Object> r : rows) {
            List<String> nr = new ArrayList<>();
            for (Object v : r) {
                nr.add(canon(v));
            }
            out.add(nr);
        }
        return out;
    }

    private List<List<String>> normalizeTrafRows(JSONArray rows) {
        List<List<String>> out = new ArrayList<>();
        if (rows == null) {
            return out;
        }
        for (int i = 0; i < rows.length(); i++) {
            JSONArray r = rows.getJSONArray(i);
            List<String> nr = new ArrayList<>();
            for (int j = 0; j < r.length(); j++) {
                Object v = r.isNull(j) ? null : r.get(j);
                nr.add(canon(v));
            }
            out.add(nr);
        }
        return out;
    }

    private static String canon(Object v) {
        if (v == null) {
            return "NULL";
        }
        if (v instanceof Number) {
            double d = ((Number) v).doubleValue();
            if (d == Math.floor(d) && !Double.isInfinite(d)) {
                return Long.toString((long) d);
            }
            return String.format("%.6g", d);
        }
        return v.toString();
    }

    private static boolean bagsEqual(List<List<String>> a, List<List<String>> b) {
        if (a.size() != b.size()) {
            return false;
        }
        List<List<String>> sa = new ArrayList<>(a);
        List<List<String>> sb = new ArrayList<>(b);
        Comparator<List<String>> cmp = (x, y) -> x.toString().compareTo(y.toString());
        Collections.sort(sa, cmp);
        Collections.sort(sb, cmp);
        return sa.equals(sb);
    }

    private void writeYaml(Path file, String sql, List<String> cols, List<List<Object>> rows, String extra) {
        StringBuilder sb = new StringBuilder();
        sb.append("engine: ").append(trafEngine).append('\n');
        sb.append("schema:\n");
        if (currentSchemaTables.isEmpty()) {
            // overwrite the "schema:" header with "schema: {}"
            sb.setLength(sb.length() - "schema:\n".length());
            sb.append("schema: {}\n");
        } else {
            for (String tname : currentSchemaTables.keySet()) {
                JSONArray scols = currentSchemaTables.getJSONArray(tname);
                sb.append("  ").append(tname).append(":\n");
                for (int i = 0; i < scols.length(); i++) {
                    JSONObject nt = scols.getJSONObject(i);
                    sb.append("    - {name: ").append(yamlScalar(nt.getString("name"))).append(", type: ")
                            .append(yamlScalar(nt.getString("type"))).append("}\n");
                }
            }
        }
        sb.append("data:\n");
        if (currentSchemaData.isEmpty()) {
            sb.setLength(sb.length() - "data:\n".length());
            sb.append("data: {}\n");
        } else {
            for (String tname : currentSchemaData.keySet()) {
                JSONArray drows = currentSchemaData.getJSONArray(tname);
                if (drows.length() == 0) {
                    sb.append("  ").append(tname).append(": []\n");
                    continue;
                }
                sb.append("  ").append(tname).append(":\n");
                for (int i = 0; i < drows.length(); i++) {
                    JSONArray row = drows.getJSONArray(i);
                    sb.append("    - [");
                    for (int j = 0; j < row.length(); j++) {
                        if (j > 0) {
                            sb.append(", ");
                        }
                        Object v = row.isNull(j) ? null : row.get(j);
                        sb.append(yamlScalar(v));
                    }
                    sb.append("]\n");
                }
            }
        }
        // List<String> setup = collectSetupSql();
        // if (setup.isEmpty()) {
        //     sb.append("setup_sql: []\n");
        // } else {
        //     sb.append("setup_sql:\n");
        //     for (String s : setup) {
        //         sb.append("  - ").append(yamlScalar(s)).append('\n');
        //     }
        // }
        sb.append("sql: ").append(yamlScalar(sql)).append('\n');
        if (cols.isEmpty()) {
            sb.append("columns: []\n");
        } else {
            sb.append("columns:\n");
            for (String c : cols) {
                sb.append("  - ").append(yamlScalar(c)).append('\n');
            }
        }
        if (rows.isEmpty()) {
            sb.append("rows: []\n");
        } else {
            sb.append("rows:\n");
            for (List<Object> r : rows) {
                sb.append("  - [");
                for (int i = 0; i < r.size(); i++) {
                    if (i > 0) {
                        sb.append(", ");
                    }
                    sb.append(yamlScalar(r.get(i)));
                }
                sb.append("]\n");
            }
        }
        if (extra != null) {
            sb.append(extra);
        }
        try {
            Files.write(file, sb.toString().getBytes(StandardCharsets.UTF_8), StandardOpenOption.CREATE,
                    StandardOpenOption.TRUNCATE_EXISTING);
        } catch (IOException e) {
            try (PrintWriter p = new PrintWriter(System.err)) {
                p.println("traf suite write failed: " + e);
            }
        }
    }

    private static String yamlScalar(Object v) {
        if (v == null) {
            return "null";
        }
        if (v instanceof Number || v instanceof Boolean) {
            return v.toString();
        }
        String s = v.toString();
        StringBuilder out = new StringBuilder("\"");
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            switch (c) {
            case '\\':
                out.append("\\\\");
                break;
            case '"':
                out.append("\\\"");
                break;
            case '\n':
                out.append("\\n");
                break;
            case '\r':
                out.append("\\r");
                break;
            case '\t':
                out.append("\\t");
                break;
            default:
                if (c < 0x20) {
                    out.append(String.format("\\x%02x", (int) c));
                } else {
                    out.append(c);
                }
            }
        }
        out.append('"');
        return out.toString();
    }

    @Override
    public Reproducer<GeneralGlobalState> getLastReproducer() {
        return reproducer;
    }

    private final class MismatchReproducer implements Reproducer<GeneralGlobalState> {
        private String msg;

        MismatchReproducer(String msg) {
            this.msg = msg;
        }

        @Override
        public String getErrorMessage() {
            return msg;
        }

        @Override
        public boolean bugStillTriggers(GeneralGlobalState globalState) {
            return true;
        }
    }
}
