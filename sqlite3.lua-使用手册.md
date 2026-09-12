# sqlite3.lua 使用手册

**纯 Lua 实现的 SQLite 数据库引擎** — 单文件、零依赖、数据库文件与真实 SQLite 完全互通。

---

## 1. 简介

`sqlite3.lua` 是一个用纯 Lua 编写的 SQLite 数据库引擎。它不依赖任何 C 库，**生成的数据库文件与官方 SQLite 格式完全兼容**：

- 用本引擎创建的 `.db` 文件，可以被官方 sqlite3 命令行、lsqlite3、Python sqlite3、DB Browser for SQLite 等任何工具直接打开、查询、修改；
- 用其他工具创建或修改过的 SQLite 文件，本引擎也能正常读写。

API 设计与 `lsqlite3`（LuaSQLite3）保持兼容，从 lsqlite3 迁移只需把 `require("lsqlite3")` 换成本模块。

## 2. 环境要求

| 项目 | 要求 |
|------|------|
| Lua 环境 | LuaJIT 2.0+（推荐，自带 `bit` 位运算库）|
| 位运算库 | 必需（LuaJIT 内置；纯 Lua 5.1 需另行提供 `bit` 库）|
| 平台 | 任意（纯 Lua，无平台相关代码）|

```bash
# 运行测试
luajit db-text.lua
```

## 3. 快速上手

```lua
local sql = dofile("sqlite3.lua")   -- 也可改为 require 形式
local db = sql.open("app.db")

-- 建表
db:exec([[
  CREATE TABLE users (
    id    INTEGER PRIMARY KEY,
    name  TEXT NOT NULL,
    age   INT DEFAULT 0,
    email TEXT UNIQUE
  )
]])

-- 插入
db:exec("INSERT INTO users VALUES(1, 'Alice', 30, 'alice@x.com')")

-- 查询 (nrows 返回以列名为键的表)
for row in db:nrows("SELECT id, name FROM users WHERE age > 25 ORDER BY name") do
  print(row.id, row.name)
end

db:close()
```

## 4. API 参考

### 4.1 模块函数

| 函数 | 说明 |
|------|------|
| `sql.open(路径)` | 打开/创建文件数据库，返回 DB 对象 |
| `sql.open_memory()` | 创建内存数据库（不落盘）|
| `sql.version()` | 返回引擎版本字符串 |
| `sql.sqlite_version()` | 返回兼容的 SQLite 版本号（"3.45.1"）|
| `sql.errmsg(db)` | 取数据库最近错误信息 |

**错误码常量**（与 SQLite 官方数值一致）：

```lua
sql.OK         -- 0    成功
sql.ROW        -- 100  有数据行 (stmt:step)
sql.DONE       -- 101  执行完毕 (stmt:step)
sql.ERROR      -- 1    SQL 错误
sql.CONSTRAINT -- 19   约束冲突 (UNIQUE/NOT NULL/主键)
```

### 4.2 DB 对象方法

#### 执行 SQL

```lua
db:exec(sql)          -- 执行 SQL(可多条, 用分号分隔)
                      -- 成功返回 0 (sql.OK), 失败返回错误码
db:errmsg()           -- 最近一次错误信息
db:errcode()          -- 最近一次错误码
```

`exec` 支持一次传入多条语句：

```lua
db:exec([[
  CREATE TABLE a(x INT);
  INSERT INTO a VALUES(1);
  INSERT INTO a VALUES(2);
]])
```

#### 查询

```lua
-- nrows: 迭代器产出 {列名=值, [序号]=值} 形式的表
for row in db:nrows("SELECT id, name FROM users") do
  print(row.id, row.name)   -- 也可以 row[1], row[2]
end

-- rows / urows: 迭代器直接产出各列值
for id, name in db:rows("SELECT id, name FROM users") do
  print(id, name)
end

-- 查询带参数
for row in db:nrows("SELECT * FROM users WHERE id = ?", {5}) do ... end
```

#### 预编译语句 (prepare/bind/step)

```lua
local stmt = db:prepare("SELECT name, age FROM users WHERE age > ?")

stmt:bind_values(25)        -- 按序号绑定多个值
stmt:step()                 -- 执行; SELECT 返回 sql.ROW

print(stmt:get_value(0))    -- 当前行第 1 列 (0 基)
print(stmt:get_values())    -- 当前行所有列
print(stmt:get_name(0))     -- 第 1 列的列名
for _, n in ipairs(stmt:columns()) do print(n) end  -- 全部列名

stmt:reset()                -- 重置, 可重新绑定执行
stmt:finalize()             -- 释放
```

**命名参数绑定：**

```lua
local stmt = db:prepare("SELECT name FROM users WHERE age > :minage LIMIT 1")
stmt:bind_names({ minage = 25 })
stmt:step()
print(stmt:get_value(0))
stmt:finalize()
```

支持的参数形式：`?`、`?N`、`:name`、`@name`、`$name`。

#### 其他

```lua
db:last_insert_rowid()  -- 最近一次 INSERT 的 rowid
db:changes()            -- 累计修改的行数 (INSERT/UPDATE/DELETE)
db:create_function(name, nargs, fn)  -- 注册自定义 SQL 函数
db:close()              -- 关闭数据库 (自动落盘)
```

### 4.3 Statement 对象方法

| 方法 | 说明 |
|------|------|
| `stmt:bind_values(v1, v2, ...)` | 按位置绑定参数 |
| `stmt:bind_names{a=1, b=2}` | 按名字绑定参数 |
| `stmt:bind(i, v)` | 绑定单个参数（1 基）|
| `stmt:step()` | 执行一步；SELECT 返回 `sql.ROW`，写语句返回 `sql.DONE`，出错返回错误码 |
| `stmt:get_value(i)` | 当前行第 i 列（0 基）|
| `stmt:get_values()` | 当前行全部列 |
| `stmt:get_name(i)` | 第 i 列的列名 |
| `stmt:columns()` | 列名列表 |
| `stmt:reset()` | 重置语句 |
| `stmt:finalize()` | 释放语句 |

## 5. SQL 支持范围

### 5.1 DDL（数据定义）

```sql
CREATE TABLE 表名 (列定义, ...)
CREATE TABLE IF NOT EXISTS 表名 (...)
CREATE INDEX 索引名 ON 表名(列, ...)
CREATE UNIQUE INDEX 索引名 ON 表名(列, ...)
DROP TABLE [IF EXISTS] 表名
DROP INDEX [IF EXISTS] 索引名
```

**列定义支持：**

- 类型：`INTEGER`、`INT`、`TEXT`、`REAL`、`FLOAT`、`DOUBLE`、`BLOB`、`NUMERIC`、`VARCHAR(n)`、`CHAR(n)`（自动归并为 SQLite 五种亲和性）
- 约束：`PRIMARY KEY [ASC|DESC] [AUTOINCREMENT]`、`NOT NULL`、`UNIQUE`、`DEFAULT 值`
- 表级约束：`PRIMARY KEY(列, ...)`、`UNIQUE(列, ...)`
- `CHECK` / `FOREIGN KEY` 语法可写但当前不强制检查

> 说明：列为 `INTEGER PRIMARY KEY` 时即 rowid 别名（与 SQLite 一致）；带 `UNIQUE` 约束的列会自动创建 `sqlite_autoindex_表名_N` 索引——与真实 SQLite 行为一致，保证文件互通。

### 5.2 DML（增删改）

```sql
INSERT INTO 表名 VALUES (...)
INSERT INTO 表名(列, ...) VALUES (...)
INSERT INTO 表名 VALUES (...), (...)           -- 多行
INSERT OR REPLACE INTO ...                     -- 冲突时替换
INSERT OR IGNORE INTO ...                      -- 冲突时忽略

UPDATE 表名 SET 列 = 表达式, ... [WHERE 条件]

DELETE FROM 表名 [WHERE 条件]
```

### 5.3 SELECT

```sql
SELECT [DISTINCT] 结果列
FROM 表 / 子查询 / JOIN
[WHERE 条件]
[GROUP BY 表达式, ...] [HAVING 条件]
[ORDER BY 表达式 [ASC|DESC], ...]
[LIMIT n [OFFSET m]]           -- 也支持 LIMIT m, n 写法
```

**FROM/JOIN 支持：**

```sql
FROM t1, t2                        -- 交叉连接
FROM a JOIN b ON a.x = b.x         -- 内连接
FROM a INNER JOIN b ON ...
FROM a LEFT JOIN b ON ...          -- 左连接
FROM a LEFT OUTER JOIN b ON ...
FROM a CROSS JOIN b
FROM (SELECT ...) AS 别名           -- 子查询作数据源
表名 AS 别名 / 表名 别名             -- 表别名
```

**WHERE 条件表达式：**

- 比较：`=` `==` `!=` `<>` `<` `<=` `>` `>=`
- 逻辑：`AND` `OR` `NOT`
- 判断：`IS NULL` `IS NOT NULL` `IS` `IS NOT`
- 集合：`IN (列表)` `IN (子查询)` `NOT IN`
- 范围：`BETWEEN a AND b`
- 模式：`LIKE`（`%` `_`，不区分 ASCII 大小写）、`GLOB`（`*` `?`）、`ESCAPE`
- 存在：`EXISTS (子查询)`

**表达式：**

- 算术：`+` `-` `*` `/` `%`（两整数相除做整除）
- 字符串拼接：`||`
- 位非：`~`，一元 `-`
- `CASE [表达式] WHEN ... THEN ... [ELSE ...] END`
- `CAST(表达式 AS 类型)`
- 标量子查询、`(值1, 值2)` 行值
- 字面量：数字（含 `0x` 十六进制）、`'字符串'`（`''` 转义）、`x'0102FF'` BLOB、`NULL`

### 5.4 事务

```sql
BEGIN [TRANSACTION]
COMMIT [TRANSACTION]
ROLLBACK [TRANSACTION]
```

事务内的修改在 `COMMIT` 时一次性落盘，`ROLLBACK` 撤销全部修改。

> 实现为**快照式事务**：`BEGIN` 时对内存状态做快照，回滚即恢复快照。适合单连接使用。

### 5.5 其他语句

- `PRAGMA ...` — 接受并忽略（如 `PRAGMA integrity_check` 可执行但不返回检查结果）
- `VACUUM` / `ANALYZE` — 接受但不做实质操作
- `CREATE VIEW` / `CREATE TRIGGER` — 不支持

## 6. 内置函数

**标量函数：**

| 函数 | 说明 |
|------|------|
| `abs(x)` | 绝对值 |
| `length(s)` | 字符/字节数 |
| `lower(s)` / `upper(s)` | 大小写转换 |
| `substr(s, start[, len])` | 子串（负索引从尾部数）|
| `replace(s, from, to)` | 替换 |
| `trim(s[, chars])` / `ltrim` / `rtrim` | 去空白或指定字符 |
| `coalesce(a, b, ...)` / `ifnull(a, b)` | 第一个非 NULL 值 |
| `nullif(a, b)` | 相等则返回 NULL |
| `typeof(v)` | 返回 integer/real/text/blob/null |
| `round(x[, d])` | 四舍五入 |
| `hex(v)` | 十六进制文本 |
| `instr(s, sub)` | 子串位置（找不到为 0）|
| `quote(v)` | SQL 字面量形式 |
| `random()` | 随机整数 |
| `sqlite_version()` | "3.45.1" |
| `char(n, ...)` / `unicode(s)` | 字符码转换 |
| `zeroblob(n)` | N 字节全零 BLOB |
| `max(a, b, ...)` / `min(a, b, ...)` | 多参数标量最值 |

**聚合函数**（配合 GROUP BY 或全表）：`count(*)`、`count(表达式)`、`sum`、`total`、`avg`、`min`、`max`、`group_concat(列[, 分隔符])`。

## 7. 数据类型与亲和性

| SQLite 类型 | Lua 类型 |
|-------------|----------|
| INTEGER | number（整数）|
| REAL | number（小数）|
| TEXT | string |
| BLOB | blob 包装值（`typeof` 为 "blob"）|
| NULL | nil |

- 按列声明的亲和性自动转换：向 INTEGER 列插入 `"42"` 字符串会存为整数 42。
- Lua 的 number 在 2⁶³ 以内且为整数值时存为 INTEGER，否则存为 REAL（与 SQLite 一致）。
- **BLOB**：SQL 中用 `x'0102FF'` 字面量写入；读出后用 `typeof()` 判别、`hex()`/`length()` 处理。
- 查询结果中 NULL 列的值为 Lua `nil`。

## 8. 自定义函数

```lua
db:create_function("lua_add", 2, function(a, b)
  return (a or 0) + (b or 0)
end)

for row in db:nrows("SELECT lua_add(3, 4) AS s") do
  print(row.s)   --> 7
end
```

- 参数个数仅作声明用途，按名字调用；
- 返回 `number`/`string`/`nil` 分别成为数值/文本/NULL；返回 `true`/`false` 转为 1/0。

## 9. 与真实 SQLite 的互通

这是本引擎的核心设计目标，经测试验证的互通场景：

```
纯 Lua 建库 ──写入──► .db 文件 ◄──读取── 官方 sqlite3 / lsqlite3 / Python / DB Browser
                        ▲                        │
                        └────── 修改后 ◄──────────┘
                                 纯 Lua 重新打开, 继续读写
```

- `PRAGMA integrity_check`（由真实 SQLite 执行）返回 **ok**；
- 表、索引（含 UNIQUE 自动索引）、溢出大行、NULL 值、freelist 空闲页等格式细节均符合官方规范；
- 推荐工作流：开发/运行用本引擎，数据分析、导出、可视化交给任何标准 SQLite 工具。

## 10. 性能参考

LuaJIT 2.1、Windows、5000 行规模实测：

| 操作 | 耗时 | 吞吐 |
|------|------|------|
| 事务内批量插入 | 3.5 s | ≈ 1,400 行/秒 |
| 建索引（5000 行）| 1.9 s | — |
| 索引点查 | — | ≈ 90 次/秒 |
| 全表聚合 count/avg | 0.02 s | — |
| 更新 500 行 | 0.16 s | — |
| 删除 1000 行 | 2.0 s | — |
| ORDER BY + LIMIT | 0.02 s | — |

适合几千至几万行的轻量数据场景（配置、缓存、日志、小型业务数据）。更大规模建议直接使用原生 SQLite。

## 11. 局限与注意事项

1. **单连接**：不支持并发访问；同一文件同时被本引擎和别的进程打开时，后写者会覆盖（无文件锁）。
2. **事务为快照式**：BEGIN 会对状态做内存快照，超大数据量的事务回滚会消耗较多内存。
3. **页满采用局部/全量重排**：数据正确，但高频页分裂场景（如随机乱序大量插入）写入速度会低于顺序插入。
4. **SELECT 子查询**不支持 `SELECT * FROM (子查询)` 的 `*` 展开，需列出列名。
5. **不支持**：VIEW、TRIGGER、窗口函数、CTE（WITH）、WITHOUT ROWID、外键强制、JSON 函数。
6. Lua number 为双精度浮点：**整数精确范围 ±2⁵³**，超过后可能丢失精度（LuaJIT 环境的固有限制）。
7. `PRAGMA` 语句被静默接受；`PRAGMA table_info` 等不返回结果。
8. 错误处理：`exec` 失败**不抛异常**，返回错误码并用 `db:errmsg()` 查询详情；`nrows` 查询失败会抛 Lua 错误。

## 12. 测试

`db-text.lua` 是完整测试集（57 项断言），覆盖：

DDL / INSERT(REPLACE·IGNORE·约束) / SELECT(WHERE·LIKE·IN·BETWEEN) / 参数绑定 / UPDATE·DELETE / 聚合·GROUP BY·HAVING / JOIN(内·左) / 子查询 / 事务回滚 / 类型·BLOB·NULL / 内置函数 / LIMIT·OFFSET·DISTINCT / 自定义函数 / DROP / 持久化重开 / **与真实 SQLite 的双向交叉验证**

```bash
luajit db-text.lua
# 输出: ALL PASS: 57 通过, 0 失败
```

测试第 [16] 节需要 `sqlite3\lsqlite3.dll`（你的目录中已具备）；缺失时该节自动跳过。

## 13. 常见问题

**Q: 如何从 lsqlite3 迁移？**
把 `require("lsqlite3")` 换成 `dofile("sqlite3.lua")`（或改造模块为 require 形式），其余 API（open/exec/nrows/prepare/bind/step）完全兼容。

**Q: 插入报 `UNIQUE 约束失败`？**
与 SQLite 一致：UNIQUE 列 / 主键出现重复值。可用 `INSERT OR IGNORE` 跳过或 `INSERT OR REPLACE` 覆盖。

**Q: INTEGER PRIMARY KEY 列读出来是 nil？**
不会。该列即 rowid，读出时自动回填；record 内部按 SQLite 规范存 NULL，对用户透明。

**Q: 为什么我的 `?` 参数查不到数据？**
检查绑定顺序与次数；`stmt:reset()` 后需重新绑定。命名参数用 `bind_names`。

**Q: 文件可以被哪些工具打开？**
任何标准 SQLite 工具：官方 `sqlite3` 命令行、DB Browser for SQLite、DBeaver、Python `sqlite3`、Go/Java/ Rust 各语言驱动等。

**Q: 怎么彻底重置数据库？**
删除 `.db` 文件后重新 `sql.open`，或 `DROP TABLE` 各表。

---

*引擎版本：lsqlite3-compatible 1.0 (pure lua) · 兼容 SQLite 3.45.1 文件格式*
