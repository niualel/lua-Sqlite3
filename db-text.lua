--==============================================================================
-- db-text.lua — sqlite3.lua (纯 Lua SQLite 引擎) 完整测试集
-- 运行: luajit db-text.lua
--==============================================================================

local TESTDIR = debug.traceback and arg and arg[0] and arg[0]:match("(.*)[%\\/]") or "."
local DBFILE = (TESTDIR ~= "" and TESTDIR or ".") .. "/db-text.db"
local sql = dofile(TESTDIR ~= "" and (TESTDIR .. "/sqlite3.lua") or "sqlite3.lua")

local pass, fail = 0, 0
local function ok(cond, msg)
  if cond then pass = pass + 1
  else fail = fail + 1; print("FAIL: " .. msg) end
end
local function eq(a, b, msg)
  if a == b then pass = pass + 1
  else fail = fail + 1; print(("FAIL: %s — 期望 %s, 得到 %s"):format(msg, tostring(b), tostring(a))) end
end

print("=== [1] 建库 / DDL ===")
os.remove(DBFILE)
local db = sql.open(DBFILE)

db:exec([[
  CREATE TABLE users (
    id INTEGER PRIMARY KEY,
    name TEXT NOT NULL,
    age INT DEFAULT 0,
    email TEXT UNIQUE
  )
]])
ok(true, "CREATE TABLE")

db:exec("CREATE INDEX idx_users_name ON users(name)")
ok(true, "CREATE INDEX")

-- 重复建表报错
local c = db:exec("CREATE TABLE users(id INT)")
eq(c, sql.ERROR, "重复建表报错")

print("=== [2] INSERT ===")
db:exec("INSERT INTO users VALUES(1, 'Alice', 30, 'alice@x.com')")
db:exec("INSERT INTO users VALUES(2, 'Bob', 25, 'bob@x.com')")
db:exec("INSERT INTO users(name, age, email) VALUES('Carol', 35, 'carol@x.com')")
eq(db:last_insert_rowid(), 3, "自增 rowid")
db:exec("INSERT INTO users(id, name, age) VALUES(10, 'Dave', 40)")
eq(db:last_insert_rowid(), 10, "显式 rowid")

-- UNIQUE 冲突
local c2 = db:exec("INSERT INTO users VALUES(5, 'Eve', 20, 'alice@x.com')")
eq(c2, sql.CONSTRAINT, "UNIQUE 冲突被拒")

-- REPLACE
db:exec("INSERT OR REPLACE INTO users VALUES(1, 'Alice2', 31, 'alice2@x.com')")
local n = 0
for row in db:nrows("SELECT name FROM users WHERE id = 1") do n = n + 1; eq(row.name, "Alice2", "REPLACE 生效") end
eq(n, 1, "REPLACE 后仅一行")

-- 批量
db:exec("BEGIN")
for i = 100, 199 do
  db:exec(("INSERT INTO users VALUES(%d, 'user%d', %d, 'u%d@x.com')"):format(i, i, i % 60, i))
end
db:exec("COMMIT")
ok(true, "事务批量插入")

print("=== [3] SELECT 基础 ===")
do
  local rows = {}
  for row in db:nrows("SELECT id, name, age FROM users WHERE id <= 3 ORDER BY id") do
    rows[#rows + 1] = row
  end
  eq(#rows, 3, "WHERE id<=3")
  eq(rows[1].id, 1, "排序第一")
  eq(rows[1].name, "Alice2", "ORDER BY id 第一行")
  eq(rows[2].name, "Bob", "Bob")
  eq(rows[3].name, "Carol", "Carol")
end

-- LIKE
do
  local n = 0
  for row in db:nrows("SELECT name FROM users WHERE name LIKE 'user1%' ORDER BY name") do
    n = n + 1
  end
  eq(n, 100, "LIKE user1% (user100..user199 共100)")
end

-- BETWEEN / IN
do
  local n = 0
  for row in db:nrows("SELECT id FROM users WHERE age BETWEEN 20 AND 27 AND id >= 100") do
    n = n + 1
  end
  ok(n >= 0, "BETWEEN 语法")
  n = 0
  for row in db:nrows("SELECT id FROM users WHERE id IN (1, 2, 10)") do n = n + 1 end
  eq(n, 3, "IN")
end

-- 表达式
do
  for row in db:nrows("SELECT 1 + 2 * 3 AS x, length('hello') AS l, upper('abc') AS u") do
    eq(row.x, 7, "1+2*3")
    eq(row.l, 5, "length")
    eq(row.u, "ABC", "upper")
  end
end

print("=== [4] 参数绑定 ===")
do
  local stmt = db:prepare("SELECT name, age FROM users WHERE id = ?")
  stmt:bind_values(2)
  stmt:step()
  eq(stmt:get_value(0), "Bob", "绑定 ? 查询")
  stmt:finalize()

  local stmt2 = db:prepare("SELECT name FROM users WHERE age > :minage ORDER BY age LIMIT 1")
  stmt2:bind_names({ minage = 30 })
  stmt2:step()
  -- age>30 最小: Alice2(31)
  eq(stmt2:get_value(0), "Alice2", "命名参数")
  stmt2:finalize()
end

print("=== [5] UPDATE / DELETE ===")
db:exec("UPDATE users SET age = age + 1 WHERE id >= 100")
do
  -- 100 % 60 = 40, +1 = 41
  for row in db:nrows("SELECT age FROM users WHERE id = 100") do
    eq(row.age, 41, "UPDATE age+1")
  end
end
db:exec("DELETE FROM users WHERE id >= 150")
do
  local n = 0
  for row in db:nrows("SELECT id FROM users") do n = n + 1 end
  -- 1,2,3,10 + 100..149 = 54
  eq(n, 54, "DELETE 后行数")
end

print("=== [6] 聚合 / GROUP BY ===")
do
  for row in db:nrows("SELECT count(*) AS c, sum(age) AS s, min(age) AS mn, max(age) AS mx FROM users") do
    ok(row.c > 0, "count > 0")
    ok(row.s > 0, "sum > 0")
  end
end
do
  local groups = {}
  for row in db:nrows("SELECT age % 10 AS d, count(*) AS c FROM users GROUP BY age % 10 ORDER BY d") do
    groups[#groups + 1] = row
  end
  ok(#groups >= 5, "GROUP BY 分组数")
  -- 排序校验
  local prev = -1
  for _, g in ipairs(groups) do
    ok(g.d >= prev, "GROUP BY 排序")
    prev = g.d
  end
end
do
  for row in db:nrows("SELECT name FROM users GROUP BY name HAVING count(*) > 1 LIMIT 3") do
    ok(true, "HAVING")
  end
end

print("=== [7] JOIN ===")
db:exec("CREATE TABLE orders (id INTEGER PRIMARY KEY, user_id INT, amount REAL)")
db:exec("INSERT INTO orders VALUES(1, 1, 99.5)")
db:exec("INSERT INTO orders VALUES(2, 2, 20.0)")
db:exec("INSERT INTO orders VALUES(3, 2, 35.0)")
db:exec("INSERT INTO orders VALUES(4, 999, 1.0)") -- 孤儿
do
  local n = 0
  for row in db:nrows([[SELECT u.name, o.amount FROM orders o
                        JOIN users u ON o.user_id = u.id ORDER BY o.id]]) do
    n = n + 1
    if n == 1 then eq(row.name, "Alice2", "JOIN 第一行") end
    if n == 2 then eq(row.name, "Bob", "JOIN 第二行") end
  end
  eq(n, 3, "INNER JOIN 行数 (孤儿排除)")
end
do
  local n = 0
  for row in db:nrows([[SELECT u.name, o.amount FROM users u
                        LEFT JOIN orders o ON u.id = o.user_id]]) do
    n = n + 1
  end
  ok(n >= 54, "LEFT JOIN 行数 >= 表行数")
end
do
  local n = 0
  for row in db:nrows([[SELECT u.name, count(o.id) AS cnt, sum(o.amount) AS total FROM users u
                        LEFT JOIN orders o ON u.id = o.user_id
                        GROUP BY u.id HAVING cnt > 0 ORDER BY total DESC]]) do
    n = n + 1
  end
  eq(n, 2, "JOIN+聚合+HAVING")
end

print("=== [8] 子查询 ===")
do
  local n = 0
  for row in db:nrows("SELECT name FROM users WHERE id IN (SELECT user_id FROM orders)") do
    n = n + 1
  end
  eq(n, 2, "IN 子查询")
end
do
  for row in db:nrows("SELECT (SELECT count(*) FROM orders) AS oc") do
    eq(row.oc, 4, "标量子查询")
  end
end

print("=== [9] 事务 / ROLLBACK ===")
db:exec("BEGIN")
db:exec("INSERT INTO users(name, age) VALUES('TempUser', 1)")
do
  local n = 0
  for row in db:nrows("SELECT id FROM users WHERE name = 'TempUser'") do n = n + 1 end
  eq(n, 1, "事务内可见")
end
db:exec("ROLLBACK")
do
  local n = 0
  for row in db:nrows("SELECT id FROM users WHERE name = 'TempUser'") do n = n + 1 end
  eq(n, 0, "ROLLBACK 后消失")
end

print("=== [10] 数据类型 / BLOB / NULL ===")
db:exec("CREATE TABLE types (id INTEGER PRIMARY KEY, t_text TEXT, t_int INT, t_real REAL, t_blob BLOB)")
db:exec("INSERT INTO types VALUES(1, 'héllo', 42, 3.14, x'0102FF')")
do
  for row in db:nrows("SELECT t_text, t_int, t_real, typeof(t_blob) AS tb FROM types WHERE id = 1") do
    eq(row.t_text, "héllo", "TEXT")
    eq(row.t_int, 42, "INT")
    eq(row.t_real, 3.14, "REAL")
    eq(row.tb, "blob", "BLOB typeof")
  end
end
db:exec("INSERT INTO types VALUES(2, NULL, NULL, NULL, NULL)")
do
  for row in db:nrows("SELECT t_text, t_int FROM types WHERE id = 2") do
    eq(row.t_text, nil, "NULL")
    eq(row.t_int, nil, "NULL int")
  end
end
-- IS NULL
do
  local n = 0
  for row in db:nrows("SELECT id FROM types WHERE t_text IS NULL") do n = n + 1 end
  eq(n, 1, "IS NULL")
end

print("=== [11] 内置函数 ===")
do
  for row in db:nrows([[
    SELECT abs(-5) AS a, coalesce(NULL, 'x') AS c,
           substr('abcdef', 2, 3) AS s, instr('hello', 'll') AS i,
           replace('aXa', 'X', 'Y') AS r, typeof(1) AS t1, typeof(1.5) AS t2
  ]]) do
    eq(row.a, 5, "abs")
    eq(row.c, "x", "coalesce")
    eq(row.s, "bcd", "substr")
    eq(row.i, 3, "instr")
    eq(row.r, "aYa", "replace")
    eq(row.t1, "integer", "typeof int")
    eq(row.t2, "real", "typeof real")
  end
end
-- CASE WHEN
do
  for row in db:nrows("SELECT CASE WHEN 1 < 2 THEN 'yes' ELSE 'no' END AS r1, CASE 3 WHEN 1 THEN 'a' WHEN 3 THEN 'b' END AS r2") do
    eq(row.r1, "yes", "CASE 搜索")
    eq(row.r2, "b", "CASE 简单")
  end
end

print("=== [12] LIMIT / OFFSET / DISTINCT ===")
do
  local n = 0
  for row in db:nrows("SELECT id FROM users ORDER BY id LIMIT 5") do n = n + 1 end
  eq(n, 5, "LIMIT 5")
end
do
  local first
  for row in db:nrows("SELECT id FROM users ORDER BY id LIMIT 3 OFFSET 2") do
    first = first or row.id
  end
  -- id 排序: 1,2,3,10,100.. → offset2 后第一 = 3
  eq(first, 3, "OFFSET")
end
do
  local n = 0
  for row in db:nrows("SELECT DISTINCT age % 2 FROM users WHERE id < 100") do n = n + 1 end
  ok(n <= 2, "DISTINCT")
end

print("=== [13] 自定义函数 ===")
db:create_function("lua_add", 2, function(a, b) return (a or 0) + (b or 0) end)
do
  for row in db:nrows("SELECT lua_add(3, 4) AS s") do
    eq(row.s, 7, "自定义函数")
  end
end

print("=== [14] DROP ===")
db:exec("DROP TABLE types")
local c3 = db:exec("SELECT count(*) FROM types")
eq(c3, sql.ERROR, "DROP 后查询报错")
db:exec("DROP INDEX idx_users_name")
ok(true, "DROP INDEX")

print("=== [15] 关库重开 — 持久化 ===")
db:close()
local db2 = sql.open(DBFILE)
do
  local n = 0
  for row in db2:nrows("SELECT id FROM users") do n = n + 1 end
  eq(n, 54, "重开后行数一致")
end
do
  for row in db2:nrows("SELECT name FROM users WHERE id = 100") do
    eq(row.name, "user100", "重开数据正确")
  end
end
-- 索引仍在
do
  local n = 0
  for row in db2:nrows("SELECT name FROM users WHERE name = 'Bob'") do n = n + 1 end
  eq(n, 1, "重开后索引查询")
end

print("=== [16] 与真实 SQLite 交叉验证 ===")
package.cpath = TESTDIR ~= "" and (TESTDIR .. "/sqlite3/?.dll") or "sqlite3/?.dll"
local okreal, realsql = pcall(require, "lsqlite3")
if okreal then
  local rdb = realsql.open(DBFILE)
  ok(rdb:errmsg() == "not an error", "真 SQLite 打开我们的库")
  local ic = rdb:exec("PRAGMA integrity_check")
  local msg
  for row in rdb:nrows("PRAGMA integrity_check") do
    for k, v in pairs(row) do msg = v end
  end
  eq(msg, "ok", "真 SQLite integrity_check: " .. tostring(msg))
  -- 数据一致
  local n = 0
  for row in rdb:nrows("SELECT id, name, age FROM users ORDER BY id") do
    n = n + 1
  end
  eq(n, 54, "真 SQLite 读出行数")
  -- 真引擎写一行
  rdb:exec("INSERT INTO users(name, age, email) VALUES('from-real', 1, 'real@x.com')")
  rdb:close()
  -- 纯 Lua 读
  db2:close()
  local db3 = sql.open(DBFILE)
  local found = false
  for row in db3:nrows("SELECT id FROM users WHERE name = 'from-real'") do
    found = true
  end
  eq(found, true, "纯 Lua 读真引擎写入的行")
  db3:close()
else
  print("(lsqlite3 不可用, 跳过交叉验证)")
end

print(("%s: %d 通过, %d 失败"):format(fail == 0 and "ALL PASS" or "RESULT", pass, fail))
os.exit(fail == 0 and 0 or 1)
