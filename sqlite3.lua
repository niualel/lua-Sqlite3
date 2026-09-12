--------------------------------------------------------------------------------
-- sqlite3.lua — 纯 Lua 实现的 SQLite 数据库引擎（文件格式与 SQLite 3 完全互通）
--
-- 依赖: LuaJIT 2.1 (bit 库) 或带 bit 库的 Lua 5.1
-- 用法与 lsqlite3 兼容:
--   local sql = require("sqlite3")
--   local db = sql.open("test.db")
--   db:exec("CREATE TABLE t(a, b)")
--   for row in db:nrows("SELECT * FROM t") do print(row.a, row.b) end
--   db:close()
--
-- 分层:
--   [1] 序列化: varint / 大端整数 / IEEE754 double / record 编解码
--   [2] Pager : 页缓存 / 文件头 / freelist / 事务快照 / 溢出页
--   [3] BTree : 表/索引 B-树 (插入/删除/查找/遍历/分裂/溢出)
--   [4] Schema: sqlite_master 读写与解析
--   [5] Lexer : SQL 词法
--   [6] Parser: SQL -> AST
--   [7] VM    : 表达式求值 / 语句执行
--   [8] API   : lsqlite3 兼容接口
--------------------------------------------------------------------------------

local assert, error, ipairs, pairs, pcall, next, select =
  assert, error, ipairs, pairs, pcall, next, select
local floor, abs, max, min, huge, frexp, ldexp =
  math.floor, math.abs, math.max, math.min, math.huge, math.frexp, math.ldexp
local sub, byte, char, rep, format, find, gsub =
  string.sub, string.byte, string.char, string.rep, string.format,
  string.find, string.gsub
local concat, insert, remove, sort = table.concat, table.insert, table.remove, table.sort
local setmetatable, getmetatable, type, tostring, tonumber =
  setmetatable, getmetatable, type, tostring, tonumber

local okbit, bit = pcall(require, "bit")
if not okbit then
  error("sqlite3.lua: 需要 bit 位运算库 (LuaJIT 内置)", 0)
end
local band, bor, bxor, lshift, rshift = bit.band, bit.bor, bit.bxor, bit.lshift, bit.rshift

-- SQLite 错误码 ---------------------------------------------------------------

local OK, ROW, DONE = 0, 100, 101
local ERROR, INTERNAL, PERM, ABORT, BUSY, LOCKED, NOMEM, READONLY, INTERRUPT,
      IOERR, CORRUPT, NOTFOUND, FULL, CANTOPEN, EMPTY, SCHEMA, TOOBIG,
      CONSTRAINT, MISMATCH, MISUSE, NOLDB, NOTADB, RANGE =
  1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 26, 25

local MT_ERR = {}
local function E(code, msg)
  return setmetatable({ code = code, message = msg or "未知错误" }, MT_ERR)
end
local function err(code, msg) error(E(code, msg), 0) end

-- BLOB 值包装: TEXT 与 BLOB 都是 Lua string, 用元表区分 BLOB --------------------

local MT_BLOB = {
  __tostring = function(b) return b[1] end,
  __eq = function(a, b) return a[1] == b[1] end,
  __len = function(b) return #b[1] end,
}
local function blob(s) return setmetatable({ s }, MT_BLOB) end
local function is_blob(v) return getmetatable(v) == MT_BLOB end
local function blobstr(v) return v[1] end

--------------------------------------------------------------------------------
-- [1] 序列化原语
--------------------------------------------------------------------------------

local TWO63   = 9223372036854775808.0    -- 2^63
local TWO64   = 18446744073709551616.0   -- 2^64
local TWOP32  = 4294967296.0

-- 读大端无符号整数 (最多 8 字节, 用 double 累乘, 2^53 内精确)
local function get_u(s, pos, n)
  local v = byte(s, pos)
  for i = 2, n do v = v * 256 + byte(s, pos + i - 1) end
  return v
end

-- 读大端有符号整数 (HALF[n] = 2^(8n-1), n ∈ {1,2,3,4,6,8})
local HALF = { [1] = 128, [2] = 32768, [3] = 8388608, [4] = 2147483648.0,
               [6] = 140737488355328.0, [8] = 9223372036854775808.0 }
local function get_i(s, pos, n)
  if n == 8 then
    -- 拆高低 32 位避免 2^64 附近的精度损失 (如 0xFFFF...FF 累加会舍入到 2^64)
    local hi = get_u(s, pos, 4)
    local lo = get_u(s, pos + 4, 4)
    if hi >= 2147483648.0 then hi = hi - 4294967296.0 end -- 高 32 位转有符号
    return hi * 4294967296.0 + lo
  end
  local v = get_u(s, pos, n)
  local half = HALF[n]
  if v >= half then v = v - half * 2 end -- 减 2^(8n)
  return v
end

local function s16(v) return char(floor(v / 256), v % 256) end
local function s32(v)
  return char(floor(v / 16777216) % 256, floor(v / 65536) % 256,
              floor(v / 256) % 256, v % 256)
end

-- 写 n 字节有符号整数 (v 必须是整数值且在范围内), 返回字符串
local function int_bytes(v, n)
  if v < 0 and n <= 6 then
    local m = 1
    for i = 1, n do m = m * 256 end
    v = v + m  -- n<=6 时精确
  end
  if v >= 0 or n <= 6 then
    local t = {}
    for i = n, 1, -1 do t[i] = char(v % 256); v = floor(v / 256) end
    return concat(t)
  end
  -- n == 8 且 v < 0: 拆高低 32 位避免 2^64 精度损失
  local a = floor(v / TWOP32)          -- 可能为负
  local b = v - a * TWOP32             -- [0, 2^32)
  if a < 0 then a = a + TWOP32 end
  return char(floor(a / 16777216) % 256, floor(a / 65536) % 256,
              floor(a / 256) % 256, a % 256,
              floor(b / 16777216) % 256, floor(b / 65536) % 256,
              floor(b / 256) % 256, b % 256)
end

-- varint 编码 (v: 非负, 或负数按 2^64 补码 best-effort)
-- 9 字节形式: 前 8 字节各携 7 位 (最高位置 1), 第 9 字节携高 8 位
local function put_varint(out, v)
  if v < 0 then v = v + TWO64 end
  if v <= 0 then out[#out + 1] = char(0); return end
  if v < 72057594037927936 then -- 2^56, 最多 8 个 7-bit 组
    local parts = {}
    while v > 0 do
      parts[#parts + 1] = v % 128
      v = floor(v / 128)
    end
    local n = #parts
    for i = n, 2, -1 do out[#out + 1] = char(parts[i] + 128) end
    out[#out + 1] = char(parts[1])
  else
    local hi = floor(v / 72057594037927936) -- 高 8 位 (< 256)
    local lo = v - hi * 72057594037927936   -- 低 56 位
    local parts = {}
    while lo > 0 do
      parts[#parts + 1] = lo % 128
      lo = floor(lo / 128)
    end
    -- 补齐 8 个 7-bit 组
    while #parts < 8 do parts[#parts + 1] = 0 end
    for i = 8, 1, -1 do out[#out + 1] = char(parts[i] + 128) end
    out[#out + 1] = char(hi)
  end
end

local function varint_str(v)
  local out = {}
  put_varint(out, v)
  return concat(out)
end

-- varint 解码: 返回 (值, 新位置)
-- 第 9 字节 (若有) 携带高 8 位: 值 = b9 * 2^56 + (前 8 字节的 7-bit 组)
local function get_varint(s, pos)
  local b = byte(s, pos); pos = pos + 1
  local v = band(b, 0x7F)
  local n = 1
  while b >= 0x80 and n < 9 do
    b = byte(s, pos); pos = pos + 1
    if n == 8 then
      v = b * 72057594037927936 + v
      n = n + 1
    else
      v = v * 128 + band(b, 0x7F)
      n = n + 1
    end
  end
  if n == 9 and v >= TWO63 then v = v - TWO64 end
  return v, pos
end

-- IEEE754 double <-> 8 字节大端 ------------------------------------------------

local function encode_double(x)
  if x ~= x then return "\127\248\0\0\0\0\0\0" end -- NaN (读回时按 NULL)
  local sign = 0
  if x < 0 or (x == 0 and 1 / x < 0) then sign = 1; x = -x end
  if x == 0 then return rep("\0", 8) end
  if x == huge then
    return char(bor(lshift(sign, 7), 0x7F), 0xF0, 0, 0, 0, 0, 0, 0)
  end
  local m, e = frexp(x)
  local exp = e - 1 + 1023
  local f
  if exp <= 0 then
    f = ldexp(x, 1074)     -- 次正规数的小数字段 (精确)
    exp = 0
  else
    f = m * 2 ^ 53 - 2 ^ 52 -- 52 位尾数字段
  end
  local b1 = bor(lshift(sign, 7), rshift(exp, 4))
  local hi4 = floor(f / 2 ^ 48)
  local b2 = bor(lshift(band(exp, 15), 4), hi4)
  local r = f - hi4 * 2 ^ 48
  local out = { char(b1, b2) }
  local sh = 2 ^ 40
  for _ = 1, 6 do
    local q = floor(r / sh)
    out[#out + 1] = char(q)
    r = r - q * sh
    sh = sh / 256
  end
  return concat(out)
end

local function decode_double(s, pos)
  local b1 = byte(s, pos)
  local sign = rshift(band(b1, 0x80), 7)
  local exp = bor(lshift(band(b1, 0x7F), 4), rshift(byte(s, pos + 1), 4))
  local f = band(byte(s, pos + 1), 0x0F)
  for i = 3, 8 do f = f * 256 + byte(s, pos + i - 1) end
  local v
  if exp == 2047 then
    if f == 0 then v = huge else v = 0 / 0 end
  elseif exp == 0 then
    if f == 0 then v = 0 else v = ldexp(f, -1074) end
  else
    v = ldexp(f + 2 ^ 52, exp - 1075)
  end
  if v ~= v then return nil end -- SQLite 把 NaN 读作 NULL
  if sign == 1 then v = -v end
  return v
end

-- record 编解码 ---------------------------------------------------------------
-- record = 头(varint总长 + 各列 serial type) + 体
-- serial type: 0=NULL 1..6=1/2/3/4/6/8字节整数 7=double 8=0 9=1
--              偶数>=12=BLOB (n-12)/2 字节  奇数>=13=TEXT (n-13)/2 字节

local INT_SIZES = { 1, 2, 3, 4, 6, 8 }

local function encode_record(vals, explicit_n)
  local nv = explicit_n or #vals
  if explicit_n then
    -- 校验中间 nil (不允许空洞)
    for i = 1, nv do
      if vals[i] == nil and vals[i + 1] ~= nil and i < nv then
        -- 允许 (encode 会写 NULL)
      end
    end
  end
  local st = {}
  local body = {}
  local blen = 0
  for i = 1, nv do
    local v = vals[i]
    local t = type(v)
    if v == nil then
      st[i] = 0
    elseif t == "number" then
      local iv = floor(v)
      if iv == v and v >= -TWO63 and v < TWO63 then
        if iv == 0 then st[i] = 8
        elseif iv == 1 then st[i] = 9
        elseif iv >= -128 and iv <= 127 then st[i] = 1
        elseif iv >= -32768 and iv <= 32767 then st[i] = 2
        elseif iv >= -8388608 and iv <= 8388607 then st[i] = 3
        elseif iv >= -2147483648 and iv <= 2147483647 then st[i] = 4
        elseif iv >= -549755813888 and iv <= 549755813887 then st[i] = 5
        else st[i] = 6 end
        if st[i] >= 1 and st[i] <= 6 then
          body[#body + 1] = int_bytes(iv, INT_SIZES[st[i]])
          blen = blen + INT_SIZES[st[i]]
        end
      else
        st[i] = 7
        body[#body + 1] = encode_double(v)
        blen = blen + 8
      end
    elseif t == "string" then
      st[i] = 13 + 2 * #v
      body[#body + 1] = v
      blen = blen + #v
    elseif is_blob(v) then
      local s = v[1]
      st[i] = 12 + 2 * #s
      body[#body + 1] = s
      blen = blen + #s
    else
      err(MISMATCH, "无法将该 Lua 值存入数据库: " .. tostring(v))
    end
  end
  -- 头部: 总长 varint (含自身) + 各 serial type varint
  local hdr = {}
  local total = 0
  for i = 1, nv do
    local vs = varint_str(st[i])
    hdr[#hdr + 1] = vs
    total = total + #vs
  end
  -- 头总长 = sizevarint 长度 + total; sizevarint 长度随 total 变化, 最多迭代 2 次
  local szlen, hs2 = 1, nil
  for _ = 1, 3 do
    hs2 = varint_str(total + szlen)
    if #hs2 == szlen then break end
    szlen = #hs2
  end
  local bodystr = concat(body)
  return hs2 .. concat(hdr) .. bodystr, #hs2 + total, #bodystr
end

local function decode_record(payload)
  local hsize, pos = get_varint(payload, 1)
  local types = {}
  while pos <= hsize do
    local t
    t, pos = get_varint(payload, pos)
    types[#types + 1] = t
  end
  pos = hsize + 1
  local vals = {}
  for i = 1, #types do
    local t = types[i]
    if t == 0 then
      vals[i] = nil
    elseif t >= 1 and t <= 6 then
      local n = INT_SIZES[t]
      vals[i] = get_i(payload, pos, n)
      pos = pos + n
    elseif t == 7 then
      vals[i] = decode_double(payload, pos)
      pos = pos + 8
    elseif t == 8 then
      vals[i] = 0
    elseif t == 9 then
      vals[i] = 1
    elseif t >= 12 and band(t, 1) == 0 then
      local n = (t - 12) / 2
      local s = sub(payload, pos, pos + n - 1)
      pos = pos + n
      vals[i] = blob(s)
    elseif t >= 13 then
      local n = (t - 13) / 2
      vals[i] = sub(payload, pos, pos + n - 1)
      pos = pos + n
    else
      err(CORRUPT, "非法 serial type: " .. t)
    end
  end
  return vals, #types
end

--------------------------------------------------------------------------------
-- [2] Pager — 页缓存 / 文件管理 / freelist / 事务
--------------------------------------------------------------------------------

local MAGIC = "SQLite format 3\0"
local SQLITE_VERSION_NUMBER = 3045001 -- 写入文件头的引擎版本

local Pager = {}
Pager.__index = Pager

-- 页内偏移工具 (页以 1 为基; 页 1 前 100 字节是文件头)
local function hdr_off(pageno) return pageno == 1 and 101 or 1 end

local function psplice(data, off, rmlen, s)
  return sub(data, 1, off - 1) .. s .. sub(data, off + rmlen)
end
local function pw16(data, off, v)
  return sub(data, 1, off - 1) .. s16(v) .. sub(data, off + 2)
end
local function pw32(data, off, v)
  return sub(data, 1, off - 1) .. s32(v) .. sub(data, off + 4)
end

function Pager.open(fname)
  local self = setmetatable({}, Pager)
  self.roots = {} -- 活动树根集合 (BTree 注册)
  self.fname = fname
  self.pages = {}         -- pageno -> 页字符串
  self.dirty = {}         -- pageno -> true
  self.n_pages = 0
  self.page_size = 4096
  self.usable = 4096      -- page_size - reserved
  self.reserved = 0
  self.freelist_head = 0
  self.freelist_count = 0
  self.schema_cookie = 0
  self.schema_format = 4
  self.user_version = 0
  self.encoding = 1       -- UTF-8
  self.change_counter = 0
  self.snapshot = nil     -- 事务快照
  self.file = nil
  self.readonly_pages = 0

  local f = io.open(fname, "rb")
  if f then
    local h = f:read(100)
    if not h or #h < 100 or sub(h, 1, 16) ~= MAGIC then
      f:close()
      err(NOTADB, ("无法打开数据库文件 (不是有效的 SQLite 文件): %s"):format(tostring(fname)))
    end
    local ps = get_u(h, 17, 2)
    if ps == 1 then ps = 65536 end
    if ps < 512 or ps > 65536 or band(ps, ps - 1) ~= 0 then
      f:close(); err(NOTADB, "非法页大小: " .. ps)
    end
    self.page_size = ps
    self.reserved = byte(h, 21)
    self.usable = ps - self.reserved
    self.change_counter = get_u(h, 25, 4)
    local npg = get_u(h, 29, 4)
    local fsize = f:seek("end") or 0
    local fnpg = floor(fsize / ps)
    self.n_pages = npg > 0 and npg or fnpg
    if self.n_pages > fnpg then self.n_pages = fnpg end
    self.freelist_head = get_u(h, 33, 4)
    self.freelist_count = get_u(h, 37, 4)
    self.schema_cookie = get_u(h, 41, 4)
    self.schema_format = get_u(h, 45, 4)
    self.user_version = get_u(h, 61, 4)
    self.encoding = get_u(h, 57, 4)
    if self.encoding ~= 1 then
      f:close(); err(NOTADB, "只支持 UTF-8 编码的数据库")
    end
    f:close()
    self.file = io.open(fname, "r+b")
    if not self.file then err(CANTOPEN, "无法以读写方式打开: " .. tostring(fname)) end
    self.new_file = false
  else
    self.new_file = true
  end
  return self
end

function Pager:close()
  if self.file then self.file:close(); self.file = nil end
  self.pages = {}
  self.dirty = {}
end

function Pager:get_page(n)
  local p = self.pages[n]
  if p ~= nil then return p end
  if n < 1 or n > self.n_pages then
    err(CORRUPT, ("引用了超出范围的页: %d (共 %d 页)"):format(n, self.n_pages))
  end
  if not self.file then err(CORRUPT, "数据库未打开") end
  self.file:seek("set", (n - 1) * self.page_size)
  local data = self.file:read(self.page_size)
  if not data or #data < self.page_size then
    err(CORRUPT, ("读取页 %d 失败"):format(n))
  end
  self.pages[n] = data
  return data
end

function Pager:set_page(n, data, is_dirty)
  self.pages[n] = data
  if is_dirty ~= false then self.dirty[n] = true end
end

-- 分配一个新页 (优先 freelist)
function Pager:alloc_page()
  local head = self.freelist_head
  if head ~= 0 and head <= self.n_pages then
    local trunk = self:get_page(head)
    local nxt = get_u(trunk, 1, 4)
    local cnt = get_u(trunk, 5, 4)
    if cnt > 0 then
      -- 取走最后一个叶子页号
      local off = 9 + (cnt - 1) * 4
      local leaf = get_u(trunk, off, 4)
      trunk = psplice(trunk, off, 4, "")
      trunk = pw32(trunk, 5, cnt - 1)
      self:set_page(head, trunk)
      self.freelist_count = self.freelist_count - 1
      return leaf
    else
      -- 空干页 (cnt == 0): 干页本身被分配, 下一干页接班
      self.freelist_head = nxt
      self.freelist_count = self.freelist_count - 1
      return head
    end
  end
  self.n_pages = self.n_pages + 1
  return self.n_pages
end

-- 释放一个页到 freelist
function Pager:free_page(n)
  local head = self.freelist_head
  if head ~= 0 and head <= self.n_pages then
    local trunk = self:get_page(head)
    local cnt = get_u(trunk, 5, 4)
    local maxleaves = floor((self.usable - 8) / 4)
    if cnt < maxleaves then
      -- 追加到当前干页
      trunk = psplice(trunk, 9 + cnt * 4, 0, s32(n))
      trunk = pw32(trunk, 5, cnt + 1)
      self:set_page(head, trunk)
      self.freelist_count = self.freelist_count + 1
      return
    end
  end
  -- 作为新干页
  local data = s32(head) .. s32(0) .. rep("\0", self.usable - 8)
  self:set_page(n, data)
  self.freelist_head = n
  self.freelist_count = self.freelist_count + 1
end

-- 事务: 快照 / 回滚 / 提交 ----------------------------------------------------

function Pager:begin_txn()
  if self.snapshot then return end
  local snap_pages = {}
  for k, v in pairs(self.pages) do snap_pages[k] = v end
  self.snapshot = {
    pages = snap_pages,
    keys = nil, -- 回滚时: 保留快照中的页, 丢弃其余缓存页
    n_pages = self.n_pages,
    freelist_head = self.freelist_head,
    freelist_count = self.freelist_count,
    schema_cookie = self.schema_cookie,
    user_version = self.user_version,
  }
end

function Pager:rollback_txn()
  local snap = self.snapshot
  if not snap then return end
  -- 丢弃快照之后新缓存/修改的页 (文件本身没写过, 重新从文件加载即可)
  local kept = {}
  for k, v in pairs(snap.pages) do kept[k] = v end
  self.pages = kept
  for k in pairs(self.dirty) do
    if snap.pages[k] == nil then self.dirty[k] = nil end
  end
  self.n_pages = snap.n_pages
  self.freelist_head = snap.freelist_head
  self.freelist_count = snap.freelist_count
  self.schema_cookie = snap.schema_cookie
  self.user_version = snap.user_version
  self.snapshot = nil
end

-- 把页内容写回文件
function Pager:flush()
  self:sweep_orphans()
  local any = false
  for _ in pairs(self.dirty) do any = true; break end
  if not any then
    self.snapshot = nil
    return
  end
  if self.new_file then
    self.file = io.open(self.fname, "w+b")
    if not self.file then err(CANTOPEN, "无法创建数据库文件: " .. tostring(self.fname)) end
    self.new_file = false
    self.change_counter = 1
  else
    self.change_counter = self.change_counter + 1
  end
  -- 更新页 1 头部字段
  local p1 = self:get_page(1)
  if #p1 < self.page_size then p1 = p1 .. rep("\0", self.page_size - #p1) end
  -- 确保 100 字节文件头存在且合法 (缓存中的页可能以全零开头)
  if sub(p1, 1, 16) ~= MAGIC then
    local psfield = self.page_size == 65536 and s16(1) or s16(self.page_size)
    local hdr100 = MAGIC                 -- 1..16  magic
      .. psfield                         -- 17..18 页大小
      .. "\1\1"                          -- 19..20 写/读版本 (legacy journal)
      .. char(self.reserved)             -- 21 保留字节
      .. "\64\32\32"                    -- 22..24 max/min payload 比, leaf payload
      .. s32(self.change_counter)        -- 25..28
      .. s32(self.n_pages)               -- 29..32
      .. s32(self.freelist_head)         -- 33..36
      .. s32(self.freelist_count)        -- 37..40
      .. s32(self.schema_cookie)         -- 41..44
      .. s32(self.schema_format)         -- 45..48
      .. s32(0)                          -- 49..52 cache size
      .. s32(0)                          -- 53..56 largest root (no autovacuum)
      .. s32(self.encoding)              -- 57..60
      .. s32(self.user_version)          -- 61..64
      .. s32(0)                          -- 65..68 vacuum
      .. s32(0)                          -- 69..72 app id
      .. rep("\0", 20)                    -- 73..92 reserved
      .. s32(self.change_counter)        -- 93..96 version-valid-for
      .. s32(SQLITE_VERSION_NUMBER)      -- 97..100
    p1 = hdr100 .. sub(p1, 101)
  end
  p1 = pw32(p1, 25, self.change_counter)
  p1 = pw32(p1, 29, self.n_pages)
  p1 = pw32(p1, 33, self.freelist_head)
  p1 = pw32(p1, 37, self.freelist_count)
  p1 = pw32(p1, 41, self.schema_cookie)
  p1 = pw32(p1, 45, self.schema_format)
  p1 = pw32(p1, 53, 0) -- 无 auto-vacuum
  p1 = pw32(p1, 57, self.encoding)
  p1 = pw32(p1, 61, self.user_version)
  p1 = pw32(p1, 93, self.change_counter)  -- version-valid-for
  p1 = pw32(p1, 97, SQLITE_VERSION_NUMBER)
  self.pages[1] = p1
  self.dirty[1] = true

  for n in pairs(self.dirty) do
    local data = self.pages[n]
    if data and #data < self.page_size then
      data = data .. rep("\0", self.page_size - #data)
      self.pages[n] = data
    end
    if data then
      self.file:seek("set", (n - 1) * self.page_size)
      self.file:write(data)
    end
  end
  self.file:flush()
  -- 文件截断到当前页数 (页只会增长, 但以防万一)
  local fsize = self.file:seek("end") or 0
  if fsize < self.n_pages * self.page_size then
    self.file:seek("set", self.n_pages * self.page_size - 1)
    self.file:write("\0")
    self.file:flush()
  end
  self.dirty = {}
  self.snapshot = nil
end

function Pager:commit_txn()
  if not self.snapshot then return end
  self:flush()
end

--------------------------------------------------------------------------------
-- [3] BTree — 表/索引 B-树
--------------------------------------------------------------------------------
-- 页类型: 13=表叶 5=表内 10=索引叶 2=索引内
-- 页头: type(1) 首空闲块(2) 单元数(2) 内容区起点(2, 0基, 0=65536) 碎片(1) [最右子树(4)]
-- 单元指针数组: 每项 2 字节, 指向 0 基页内偏移, 按 key 升序
-- 表叶 cell:  varint(payload长) varint(rowid) payload[本地部分] [u32 溢出页]
-- 表内 cell:  u32(左子页) varint(key=rowid)
-- 索引叶 cell: varint(payload长) payload[本地] [u32 溢出页]
-- 索引内 cell: u32(左子页) varint(payload长) payload[本地] [u32 溢出页]
-- 溢出页: u32(下一溢出页) 数据(最多 usable-4)
--
-- 语义 (经真实 SQLite dump 验证):
--   表内 cell 的 key 是其左子树中的最大 rowid;
--   查找 k: 取第一个 key >= k 的 cell 进入其左子树, 否则进最右子树。

local PT_TLEAF, PT_TINT, PT_ILEAF, PT_IINT = 13, 5, 10, 2

local BTree = {}
BTree.__index = BTree

local function bt_new(pager, root, kind)
  local bt = setmetatable({ pager = pager, root = root, kind = kind }, BTree)
  pager.roots[bt] = root or 0
  return bt
end

local function pg_ncells(pg, hoff) return get_u(pg, hoff + 3, 2) end
local function pg_content(pg, hoff)
  local c = get_u(pg, hoff + 5, 2)
  if c == 0 then c = 65536 end
  return c
end
local function is_interior(t) return t == PT_TINT or t == PT_IINT end
local function hdr_len(t) return is_interior(t) and 12 or 8 end

-- 第 i 个 cell 的 0 基偏移 (i 从 1 开始)
local function cell_off(pg, hoff, hlen, i)
  return get_u(pg, hoff + hlen + (i - 1) * 2, 2)
end

--------------------------------------------------------------------------------
-- 值比较 (SQLite 排序: NULL < 数值 < TEXT < BLOB; 同类按值/memcmp)
--------------------------------------------------------------------------------

local function class_of(v)
  if v == nil then return 0 end
  local t = type(v)
  if t == "number" then return 1 end
  if t == "string" then return 2 end
  return 3 -- blob
end

local function memcomp(a, b)
  if a == b then return 0 end
  local la, lb = #a, #b
  local n = la < lb and la or lb
  for i = 1, n do
    local da, db = byte(a, i), byte(b, i)
    if da < db then return -1 elseif da > db then return 1 end
  end
  if la < lb then return -1 elseif la > lb then return 1 end
  return 0
end

local function value_compare(a, b)
  local ca, cb = class_of(a), class_of(b)
  if ca ~= cb then return ca < cb and -1 or 1 end
  if ca == 0 then return 0 end
  if ca == 1 then
    if a < b then return -1 elseif a > b then return 1 else return 0 end
  end
  if is_blob(a) then a = a[1] end
  if is_blob(b) then b = b[1] end
  return memcomp(a, b)
end

-- record 比较: 逐列比较, 前缀相同者短的小
local function record_compare(ra, rb)
  local na, nb = #ra, #rb
  local n = na < nb and na or nb
  for i = 1, n do
    local c = value_compare(ra[i], rb[i])
    if c ~= 0 then return c end
  end
  if na == nb then return 0 end
  return na < nb and -1 or 1
end

--------------------------------------------------------------------------------
-- 溢出页
--------------------------------------------------------------------------------

local function ovf_maxlocal(bt, is_table_leaf)
  local usable = bt.pager.usable
  if is_table_leaf then return usable - 35 end
  return floor((usable - 12) * 64 / 255) - 23
end

local function ovf_minlocal(bt)
  local usable = bt.pager.usable
  return floor((usable - 12) * 32 / 255) - 23
end

-- 计算本地字节数 (独立版, pager 清扫用)
local function local_size_bt(pager, payload_len, is_table_leaf)
  local usable = pager.usable
  local X = is_table_leaf and (usable - 35) or (floor((usable - 12) * 64 / 255) - 23)
  if payload_len <= X then return payload_len end
  local M = floor((usable - 12) * 32 / 255) - 23
  local K = M + (payload_len - M) % (usable - 4)
  if K <= X then return K end
  return M
end

-- 计算本地字节数
local function local_size(bt, payload_len, is_table_leaf)
  local usable = bt.pager.usable
  local X = ovf_maxlocal(bt, is_table_leaf)
  if payload_len <= X then return payload_len end
  local M = ovf_minlocal(bt)
  local K = M + (payload_len - M) % (usable - 4)
  if K <= X then return K end
  return M
end

-- 写溢出链 (data 中 [skip+1..] 部分), 返回首页号
local function write_overflow(bt, data, skip)
  local usable = bt.pager.usable
  local per = usable - 4
  local rest = sub(data, skip + 1)
  if #rest == 0 then return 0 end
  local pages = {}
  while #rest > 0 do
    pages[#pages + 1] = bt.pager:alloc_page()
    rest = sub(rest, per + 1)
  end
  local rest2 = sub(data, skip + 1)
  for i = 1, #pages do
    local nxt = pages[i + 1] or 0
    local chunk = sub(rest2, 1, per)
    bt.pager:set_page(pages[i],
      s32(nxt) .. chunk .. rep("\0", usable - 4 - #chunk))
    rest2 = sub(rest2, per + 1)
  end
  return pages[1]
end

-- 读溢出链
local function read_overflow(bt, first, need)
  local usable = bt.pager.usable
  local parts = {}
  local pgno = first
  local total = 0
  while pgno ~= 0 do
    if pgno < 1 or pgno > bt.pager.n_pages then
      err(CORRUPT, "非法溢出页号: " .. tostring(pgno))
    end
    local pg = bt.pager:get_page(pgno)
    local take = need - total
    if take > usable - 4 then take = usable - 4 end
    parts[#parts + 1] = sub(pg, 5, 4 + take)
    total = total + take
    pgno = get_u(pg, 1, 4)
  end
  return concat(parts)
end

-- 释放溢出链
local function free_overflow(bt, first)
  local pgno = first
  while pgno ~= 0 do
    local pg = bt.pager:get_page(pgno)
    local nxt = get_u(pg, 1, 4)
    bt.pager:free_page(pgno)
    pgno = nxt
  end
end

--------------------------------------------------------------------------------
-- cell 解析 (返回字段表)
--------------------------------------------------------------------------------

-- 解析表叶 cell @pos(1基): psz, rowid, payload
local function parse_table_leaf(bt, pg, pos)
  local psz, p = get_varint(pg, pos)
  local rowid, p2 = get_varint(pg, p)
  local localn = local_size(bt, psz, true)
  local payload
  if localn == psz then
    payload = sub(pg, p2, p2 + psz - 1)
  else
    local ovf = get_u(pg, p2 + localn, 4)
    payload = sub(pg, p2, p2 + localn - 1) .. read_overflow(bt, ovf, psz - localn)
  end
  return { psz = psz, rowid = rowid, payload = payload }
end

-- 解析表内 cell: child, key
local function parse_table_int(pg, pos)
  local key = get_varint(pg, pos + 4)
  return { child = get_u(pg, pos, 4), key = key }
end

-- 解析索引 cell (叶与内通用)
local function parse_index_cell(bt, pg, pos, interior)
  local p = pos
  local child
  if interior then
    child = get_u(pg, p, 4)
    p = p + 4
  end
  local psz, p2 = get_varint(pg, p)
  local localn = local_size(bt, psz, false)
  local payload
  if localn == psz then
    payload = sub(pg, p2, p2 + psz - 1)
  else
    local ovf = get_u(pg, p2 + localn, 4)
    payload = sub(pg, p2, p2 + localn - 1) .. read_overflow(bt, ovf, psz - localn)
  end
  return { child = child, psz = psz, payload = payload }
end

-- cell 总长度 (字节)
local function cell_total_len(bt, pg, pos, ptype)
  if ptype == PT_TINT then
    local _, p2 = get_varint(pg, pos + 4)
    return p2 - pos
  end
  local p = pos
  if ptype == PT_IINT then p = p + 4 end
  local psz, p2 = get_varint(pg, p)
  if ptype == PT_TLEAF then
    local _, p3 = get_varint(pg, p2) -- rowid varint 长度也要计入
    p2 = p3
  end
  local localn = local_size(bt, psz, ptype == PT_TLEAF)
  return (p2 - pos) + localn + (localn < psz and 4 or 0)
end

--------------------------------------------------------------------------------
-- 页内空间管理
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 页内空间管理 (紧凑重建策略)
-- 每次插入/删除都对整页做一次紧凑重建:
--   [页头][指针数组][空隙][cell 紧凑置于页尾]
-- 优点: 永远没有 freeblock/碎片, 偏移永远一致; 解析真实库中带碎片的页后自动紧凑化。
--------------------------------------------------------------------------------

-- 解析页面: 返回 ptype, cells(原始字节串, 按序), rightmost(内部页)
local function page_cells(bt, pageno)
  local pg = bt.pager:get_page(pageno)
  local hoff = hdr_off(pageno)
  local ptype = byte(pg, hoff)
  local hlen = hdr_len(ptype)
  local ncells = pg_ncells(pg, hoff)
  local cells = {}
  for i = 1, ncells do
    local pos = cell_off(pg, hoff, hlen, i) + 1
    local len = cell_total_len(bt, pg, pos, ptype)
    cells[i] = sub(pg, pos, pos + len - 1)
  end
  local rm = is_interior(ptype) and get_u(pg, hoff + 8, 4) or nil
  return ptype, cells, rm
end

-- 从原始 cell 字节串提取溢出页号 (0 = 无)
local function cell_ovf_of(bt, cellstr, ptype)
  if ptype == PT_TINT then return 0 end
  local p = 1
  if ptype == PT_IINT then p = p + 4 end
  local psz, p2 = get_varint(cellstr, p)
  if ptype == PT_TLEAF then
    local _, p3 = get_varint(cellstr, p2) -- rowid
    p2 = p3
  end
  local localn = local_size(bt, psz, ptype == PT_TLEAF)
  if localn < psz then
    return get_u(cellstr, p2 + localn, 4)
  end
  return 0
end

-- 整页紧凑重建; 放不下返回 false (页面保持原状)
local function page_rebuild(bt, pageno, ptype, cells, rightmost)
  local pager = bt.pager
  local cap = pager.usable - (pageno == 1 and 100 or 0) -- cell 总容量
  local contentend = pager.page_size                       -- 内容区结束 (页尾, 绝对)
  local hlen = hdr_len(ptype)
  local n = #cells
  local total = 0
  for i = 1, n do total = total + #cells[i] end
  if hlen + n * 2 + total > cap then return false end
  local content = contentend - total -- 0 基绝对偏移的内容区起点
  local out = {}
  if pageno == 1 then out[#out + 1] = sub(pager:get_page(1), 1, 100) end
  local head
  if is_interior(ptype) then
    head = char(ptype) .. s16(0) .. s16(n) ..
           (content >= 65536 and s16(0) or s16(content)) .. char(0) .. s32(rightmost or 0)
  else
    head = char(ptype) .. s16(0) .. s16(n) ..
           (content >= 65536 and s16(0) or s16(content)) .. char(0)
  end
  out[#out + 1] = head
  local ptrs = {}
  local cur = content
  for i = 1, n do
    ptrs[i] = s16(cur)
    cur = cur + #cells[i]
  end
  out[#out + 1] = concat(ptrs)
  local helem = (pageno == 1 and 100 or 0) + #head + n * 2
  if content > helem then out[#out + 1] = rep("\0", content - helem) end
  for i = 1, n do out[#out + 1] = cells[i] end
  local np = concat(out)
  if #np < pager.page_size then np = np .. rep("\0", pager.page_size - #np) end
  pager:set_page(pageno, np)
  return true
end

-- 在页面的第 idx 位置插入 cell (字节串), 返回 true/false(空间不足)
local function page_insert_cell(bt, pageno, idx, cellstr)
  local ptype, cells, rm = page_cells(bt, pageno)
  insert(cells, idx, cellstr)
  return page_rebuild(bt, pageno, ptype, cells, rm)
end

-- 删除页面第 idx 个 cell (返回其 0 基偏移与长度; caller 负责溢出链)
local function page_delete_cell(bt, pageno, idx)
  local ptype, cells, rm = page_cells(bt, pageno)
  local cellstr = cells[idx]
  assert(cellstr, "删除不存在的 cell")
  remove(cells, idx)
  local ok = page_rebuild(bt, pageno, ptype, cells, rm)
  assert(ok, "内部错误: 重建删除后的页面失败")
  local ovf = cell_ovf_of(bt, cellstr, ptype)
  if ovf ~= 0 then free_overflow(bt, ovf) end
end

-- 新建空页
local function init_page(bt, pageno, ptype)
  page_rebuild(bt, pageno, ptype, {}, 0)
end

--------------------------------------------------------------------------------
-- BTree 高层操作
--------------------------------------------------------------------------------

-- 分裂点选择: 保证两侧页面都放得下, 并尽量均衡
-- sizes[i]: 第 i 个元素字节数; hlen: 页头长(8叶/12内); usable: 页可用字节
-- right_skip: 内部分裂时 =1 (第 m+1 个作为 divider 上移, 不入两侧)
-- 返回 m ∈ [1, n-1-right_skip]
local function choose_m_fit(bt, sizes, hlen, usable, right_skip)
  local n = #sizes
  local last = n - 1 - right_skip
  if last < 1 then return 1 end
  local pre = { 0 }
  for i = 1, n do pre[i + 1] = pre[i] + sizes[i] end
  local total = pre[n + 1]
  local function fits(cnt, bytes)
    return hlen + cnt * 2 + bytes <= usable
  end
  -- 扫描所有合法 m, 取与总量一半偏差最小者
  local best, bestd = nil, huge
  for m = 1, last do
    local lbytes = pre[m + 1]
    local rbytes = total - pre[m + 1 + right_skip]
    local rcnt = n - m - right_skip
    if fits(m, lbytes) and fits(rcnt, rbytes) then
      local dev = abs(lbytes - total / 2)
      if dev < bestd then best, bestd = m, dev end
    end
  end
  return best or 1
end

-- 字节串数组的分裂点 (叶分裂)
local function choose_m_raw(bt, cells, hlen, usable, right_skip)
  local sizes = {}
  for i = 1, #cells do sizes[i] = #cells[i] end
  return choose_m_fit(bt, sizes, hlen, usable, right_skip or 0)
end

-- 表: 下降, 返回 path(内部页栈), 叶页号, 插入/命中位置, 是否命中
-- path[i] = {pageno, cellidx, key}: cellidx 为 path[i] 页中指向 path[i+1] 的 cell
--   (key 为该 cell 的 key; 经 rightmost 下降时 key=nil)
local function table_descend(bt, rowid)
  local pager = bt.pager
  local path = {}
  local pageno = bt.root
  while true do
    local pg = pager:get_page(pageno)
    local hoff = hdr_off(pageno)
    local ptype = byte(pg, hoff)
    local hlen = hdr_len(ptype)
    local ncells = pg_ncells(pg, hoff)
    if ptype == PT_TINT then
      local lo, hi, idx = 1, ncells, ncells + 1
      local key
      while lo <= hi do
        local mid = floor((lo + hi) / 2)
        local pos = cell_off(pg, hoff, hlen, mid) + 1
        local k = get_varint(pg, pos + 4)
        if k >= rowid then idx = mid; key = k; hi = mid - 1
        else lo = mid + 1 end
      end
      local child
      if idx <= ncells then
        child = get_u(pg, cell_off(pg, hoff, hlen, idx) + 1, 4)
      else
        child = get_u(pg, hoff + 8, 4)
        key = nil
      end
      path[#path + 1] = { pageno = pageno, cellidx = idx, key = key }
      pageno = child
    elseif ptype == PT_TLEAF then
      local lo, hi, pos_idx = 1, ncells, ncells + 1
      while lo <= hi do
        local mid = floor((lo + hi) / 2)
        local pos = cell_off(pg, hoff, hlen, mid) + 1
        local psz, p = get_varint(pg, pos)
        local rid = get_varint(pg, p)
        if rid == rowid then
          return path, pageno, mid, true
        elseif rid < rowid then lo = mid + 1
        else pos_idx = mid; hi = mid - 1 end
      end
      return path, pageno, pos_idx, false
    else
      err(CORRUPT, "表树的页类型非法: " .. ptype)
    end
  end
end

-- 重建表内部页 (cells = {{child=,key=}}, rightmost); 放不下返回 false
local function rebuild_tint(bt, pageno, cells, rightmost)
  local pager = bt.pager
  init_page(bt, pageno, PT_TINT)
  local pg = pager:get_page(pageno)
  pg = pw32(pg, hdr_off(pageno) + 8, rightmost)
  pager:set_page(pageno, pg)
  for i = 1, #cells do
    if not page_insert_cell(bt, pageno, i,
        s32(cells[i].child) .. varint_str(cells[i].key)) then
      return false
    end
  end
  return true
end


-- 构造表叶 cell
local function make_tleaf_cell(bt, rowid, payload)
  local out = {}
  put_varint(out, #payload)
  put_varint(out, rowid)
  local localn = local_size(bt, #payload, true)
  if localn < #payload then
    local first = write_overflow(bt, payload, localn)
    out[#out + 1] = sub(payload, 1, localn)
    out[#out + 1] = s32(first)
  else
    out[#out + 1] = payload
  end
  return concat(out)
end

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 全树重排 (bulk rebuild): 页满时收集全部条目, 释放所有旧页, 重新贪心建树
-- 简单、正确性易证; 页数多时开销 O(N), 触发频率低 (每页满才触发一次)
--------------------------------------------------------------------------------

-- 清扫表树中的空叶 (真 SQLite 不留空叶; interior 空子树收缩)
-- 返回是否发生了变化
function BTree:prune_empty()
  local pager = self.pager
  local changed = false
  local function prune(pageno)
    -- 返回: 该子树是否全空 (可整体移除)
    local pg = pager:get_page(pageno)
    local hoff = hdr_off(pageno)
    local ptype = byte(pg, hoff)
    if ptype == PT_TINT then
      local hlen = 12
      local ncells = pg_ncells(pg, hoff)
      local rm = get_u(pg, hoff + 8, 4)
      local cells = {}
      for i = 1, ncells do
        local pos = cell_off(pg, hoff, hlen, i) + 1
        cells[i] = { child = get_u(pg, pos, 4), key = get_varint(pg, pos + 4) }
      end
      -- 递归清扫子树
      local keep = {}
      local rmkeep = prune(rm)
      for i, c in ipairs(cells) do
        if not prune(c.child) then
          keep[#keep + 1] = c
        end
      end
      if #keep == 0 and rmkeep then
        -- 整个内部页空
        return true
      end
      -- 若 rightmost 空但仍有 cell: 最后一个 cell 的 child 变新 rightmost
      if rmkeep then
        if #keep > 0 then
          local last = keep[#keep]
          rm = last.child
          keep[#keep] = nil
          rebuild_tint(self, pageno, keep, rm)
        else
          -- 只有空 rm: 整页收缩为一个空叶
          init_page(self, pageno, PT_TLEAF)
        end
        changed = true
      elseif #keep ~= #cells then
        rebuild_tint(self, pageno, keep, rm)
        changed = true
      end
      return false
    elseif ptype == PT_TLEAF then
      return pg_ncells(pg, hoff) == 0
    end
    return false
  end
  local rootempty = prune(self.root)
  if rootempty and self.root ~= 1 then
    -- 整树空: 保留根为空叶
    init_page(self, self.root, PT_TLEAF)
    changed = true
  end
  return changed
end

-- 表: 全量收集 (rowid -> payload) 按序, 重建
function BTree:rebuild_table(entries)
  -- entries: { {rowid, payload}, ... } 已按 rowid 升序
  local pager = self.pager
  -- 释放旧树所有页
  self:drop()
  -- 贪心分叶
  local usable = pager.usable
  local groups, cur, curbytes = {}, {}, 0
  for i = 1, #entries do
    local cellstr = make_tleaf_cell(self, entries[i][1], entries[i][2])
    if #cur > 0 and 8 + (#cur + 1) * 2 + curbytes + #cellstr > usable then
      groups[#groups + 1] = cur; cur, curbytes = {}, 0
    end
    cur[#cur + 1] = cellstr
    curbytes = curbytes + #cellstr
    assert(8 + #cur * 2 + curbytes <= usable, "行太大, 单页放不下")
  end
  if #cur > 0 then groups[#groups + 1] = cur end
  if #groups == 0 then
    -- 空树
    local root = pager:alloc_page()
    init_page(self, root, PT_TLEAF)
    self.root = root
    return
  end
  -- 建叶
  local leaves, keys = {}, {}
  for gi = 1, #groups do
    local p = pager:alloc_page()
    init_page(self, p, PT_TLEAF)
    for j = 1, #groups[gi] do
      assert(page_insert_cell(self, p, j, groups[gi][j]))
    end
    leaves[gi] = p
    local cs = groups[gi][#groups[gi]]
    local psz, q = get_varint(cs, 1)
    keys[gi] = (get_varint(cs, q))
  end
  -- 自底向上建内部层
  local level_pages, level_keys = leaves, keys
  while #level_pages > 1 do
    local npages, nkeys = {}, {}
    local i = 1
    while i <= #level_pages do
      -- 一页内部节点收若干子页 (目标: 子指针数 ≈ floor(usable/8), 留余量)
      local maxc = floor(usable / 10)
      local cnt = min(maxc, #level_pages - i + 1)
      local p = pager:alloc_page()
      init_page(self, p, PT_TINT)
      local rm
      for j = 1, cnt do
        if j == cnt and i + cnt - 1 == #level_pages then
          rm = level_pages[i + j - 1]
        else
          assert(page_insert_cell(self, p, j,
            s32(level_pages[i + j - 1]) .. varint_str(level_keys[i + j - 1])))
        end
      end
      if not rm then rm = level_pages[i + cnt - 1] end
      local pgx = pager:get_page(p)
      pgx = pw32(pgx, hdr_off(p) + 8, rm)
      pager:set_page(p, pgx)
      npages[#npages + 1] = p
      nkeys[#nkeys + 1] = level_keys[i + cnt - 1]
      i = i + cnt
    end
    -- 修正: 内部页的 cell child 不能是本页 rightmost (上面逻辑: 最后一个子作为 rm)
    level_pages, level_keys = npages, nkeys
  end
  self.root = level_pages[1]
  self.pager.roots[self] = self.root
end

function BTree:insert_table(rowid, payload)
  local _, _, _, found = table_descend(self, rowid)
  if found then
    err(CONSTRAINT, "UNIQUE 约束失败: rowid " .. tostring(rowid) .. " 已存在")
  end
  local cellstr = make_tleaf_cell(self, rowid, payload)
  local path, leaf, pos_idx = table_descend(self, rowid)
  if page_insert_cell(self, leaf, pos_idx, cellstr) then return end
  -- 页满: 局部重排 (父页的所有子叶合并重分组)
  if #path == 0 then
    local entries = {}
    for rid, pl in self:iter_table() do
      entries[#entries + 1] = { rid, pl }
    end
    local lo, hi, at = 1, #entries, #entries + 1
    while lo <= hi do
      local mid = floor((lo + hi) / 2)
      if entries[mid][1] < rowid then lo = mid + 1
      else at = mid; hi = mid - 1 end
    end
    insert(entries, at, { rowid, payload })
    self:rebuild_table(entries)
    return
  end
  local node = path[#path]
  local pg = self.pager:get_page(node.pageno)
  local hoff = hdr_off(node.pageno)
  local ncells = pg_ncells(pg, hoff)
  -- 收集所有子叶条目
  local children = {}
  for i = 1, ncells do
    local pos = cell_off(pg, hoff, 12, i) + 1
    children[i] = get_u(pg, pos, 4)
  end
  children[ncells + 1] = get_u(pg, hoff + 8, 4)
  local allcells = {}
  for ci = 1, #children do
    local pageno = children[ci]
    local lpg = self.pager:get_page(pageno)
    local lhoff = hdr_off(pageno)
    local ln = pg_ncells(lpg, lhoff)
    for i = 1, ln do
      local pos = cell_off(lpg, lhoff, 8, i) + 1
      local cell = parse_table_leaf(self, lpg, pos)
      allcells[#allcells + 1] = { cell.rowid, cell.payload }
    end
  end
  -- 二分插入新行
  local lo, hi, at = 1, #allcells, #allcells + 1
  while lo <= hi do
    local mid = floor((lo + hi) / 2)
    if allcells[mid][1] < rowid then lo = mid + 1
    else at = mid; hi = mid - 1 end
  end
  insert(allcells, at, { rowid, payload })
  -- 重新分组 (目标每组 ≤ 2/3 页, 减少后续触发)
  local usable = self.pager.usable
  local limit = floor(usable * 2 / 3)
  local groups, cur, curbytes = {}, {}, 0
  for i = 1, #allcells do
    local cs = make_tleaf_cell(self, allcells[i][1], allcells[i][2])
    if #cur > 0 and 8 + (#cur + 1) * 2 + curbytes + #cs > limit then
      groups[#groups + 1] = cur; cur, curbytes = {}, 0
    end
    cur[#cur + 1] = cs
    curbytes = curbytes + #cs
    assert(8 + #cur * 2 + curbytes <= usable, "行太大, 单页放不下")
  end
  if #cur > 0 then groups[#groups + 1] = cur end
  -- 写回
  local k = #groups
  local pages, keys = {}, {}
  for i = 1, k do
    local p = (i <= #children) and children[i] or self.pager:alloc_page()
    init_page(self, p, PT_TLEAF)
    local g = groups[i]
    for j = 1, #g do
      assert(page_insert_cell(self, p, j, g[j]), "局部重排失败")
    end
    pages[i] = p
    local cs = g[#g]
    local psz, q = get_varint(cs, 1)
    keys[i] = (get_varint(cs, q))
  end
  -- 释放多余子页
  for i = k + 1, #children do self.pager:free_page(children[i]) end
  -- 重建父页
  local rc = {}
  for i = 1, k - 1 do rc[i] = { child = pages[i], key = keys[i] } end
  if rebuild_tint(self, node.pageno, rc, pages[k]) then return end
  -- 父页也放不下 (极罕见): 先释放本次新分配的页, 再全树重排兜底
  for i = #children + 1, k do self.pager:free_page(pages[i]) end
  local entries = {}
  for rid, pl in self:iter_table() do
    entries[#entries + 1] = { rid, pl }
  end
  self:rebuild_table(entries)
end
function BTree:delete_table(rowid)
  local path, leaf, idx, found = table_descend(self, rowid)
  if not found then return false end
  page_delete_cell(self, leaf, idx)
  -- 修正父链 key: 若删除的是叶中最大 rowid, 父页 cell key 需更新为新 max
  local pg = self.pager:get_page(leaf)
  local hoff = hdr_off(leaf)
  local ncells = pg_ncells(pg, hoff)
  if ncells == 0 then return true end -- 空叶, key 修正由上层处理 (interior key 语义仍需, 但留待重建)
  local lastpos = cell_off(pg, hoff, 8, ncells) + 1
  local _, lp = get_varint(pg, lastpos)
  local newmax = (get_varint(pg, lp))
  for li = #path, 1, -1 do
    local node = path[li]
    local ipg = self.pager:get_page(node.pageno)
    local ihoff = hdr_off(node.pageno)
    if node.key ~= nil and node.cellidx and node.cellidx <= pg_ncells(ipg, ihoff) then
      local cpos = cell_off(ipg, ihoff, 12, node.cellidx) + 1
      local ckey = get_varint(ipg, cpos + 4)
      if ckey > newmax then
        -- 更新 key (cell 重建)
        local child = get_u(ipg, cpos, 4)
        local clen = cell_total_len(self, ipg, cpos, PT_TINT)
        local cellstr = sub(ipg, cpos, cpos + clen - 1)
        local newcell = s32(child) .. varint_str(newmax)
        -- 等长替换不保证, 走 page 重建
        local ptype2, cells2, rm2 = page_cells(self, node.pageno)
        -- 找到该 child 的 cell 更新
        for ci, c in ipairs(cells2) do
          if get_u(c, 1, 4) == child then
            cells2[ci] = s32(child) .. varint_str(newmax)
            break
          end
        end
        page_rebuild(self, node.pageno, ptype2, cells2, rm2)
      end
      -- 继续向上 (新 max 可能小于更上层 key)
    end
  end
  return true
end

function BTree:search_table(rowid)
  local pageno = self.root
  while true do
    local pg = self.pager:get_page(pageno)
    local hoff = hdr_off(pageno)
    local ptype = byte(pg, hoff)
    local hlen = hdr_len(ptype)
    local ncells = pg_ncells(pg, hoff)
    if ptype == PT_TLEAF then
      local lo, hi = 1, ncells
      while lo <= hi do
        local mid = floor((lo + hi) / 2)
        local pos = cell_off(pg, hoff, hlen, mid) + 1
        local psz, p = get_varint(pg, pos)
        local rid = get_varint(pg, p)
        if rid == rowid then
          return parse_table_leaf(self, pg, pos).payload
        elseif rid < rowid then lo = mid + 1
        else hi = mid - 1 end
      end
      return nil
    elseif ptype == PT_TINT then
      local lo, hi, idx = 1, ncells, ncells + 1
      while lo <= hi do
        local mid = floor((lo + hi) / 2)
        local pos = cell_off(pg, hoff, hlen, mid) + 1
        local key = get_varint(pg, pos + 4)
        if key >= rowid then idx = mid; hi = mid - 1
        else lo = mid + 1 end
      end
      if idx <= ncells then
        pageno = get_u(pg, cell_off(pg, hoff, hlen, idx) + 1, 4)
      else
        pageno = get_u(pg, hoff + 8, 4)
      end
    else
      err(CORRUPT, "表树的页类型非法: " .. ptype)
    end
  end
end

function BTree:max_rowid()
  local pageno = self.root
  while true do
    local pg = self.pager:get_page(pageno)
    local hoff = hdr_off(pageno)
    local ptype = byte(pg, hoff)
    if ptype == PT_TINT then
      pageno = get_u(pg, hoff + 8, 4)
    elseif ptype == PT_TLEAF then
      local ncells = pg_ncells(pg, hoff)
      if ncells == 0 then return nil end
      local pos = cell_off(pg, hoff, 8, ncells) + 1
      local psz, p = get_varint(pg, pos)
      return (get_varint(pg, p))
    else
      err(CORRUPT, "表树的页类型非法: " .. ptype)
    end
  end
end

-- 表遍历: 返回迭代器函数 () -> rowid, payload
function BTree:iter_table()
  local pager = self.pager
  local stack = {}
  local function push_leftmost(pageno)
    local p = pageno
    while true do
      local pg = pager:get_page(p)
      local hoff = hdr_off(p)
      local ptype = byte(pg, hoff)
      if ptype == PT_TINT then
        local ncells = pg_ncells(pg, hoff)
        if ncells == 0 then
          p = get_u(pg, hoff + 8, 4)
        else
          stack[#stack + 1] = { pageno = p, next_cell = 2 }
          local pos = cell_off(pg, hoff, 12, 1) + 1
          p = get_u(pg, pos, 4)
        end
      else
        stack[#stack + 1] = { pageno = p, next_cell = 1 }
        return
      end
    end
  end
  push_leftmost(self.root)
  return function()
    while #stack > 0 do
      local top = stack[#stack]
      local pg = pager:get_page(top.pageno)
      local hoff = hdr_off(top.pageno)
      local ptype = byte(pg, hoff)
      local ncells = pg_ncells(pg, hoff)
      if ptype == PT_TLEAF then
        if top.next_cell <= ncells then
          local pos = cell_off(pg, hoff, 8, top.next_cell) + 1
          top.next_cell = top.next_cell + 1
          local cell = parse_table_leaf(self, pg, pos)
          return cell.rowid, cell.payload
        end
        stack[#stack] = nil
      else
        if top.next_cell <= ncells then
          local pos = cell_off(pg, hoff, 12, top.next_cell) + 1
          local child = get_u(pg, pos, 4)
          top.next_cell = top.next_cell + 1
          push_leftmost(child)
        else
          local child = get_u(pg, hoff + 8, 4)
          stack[#stack] = nil
          push_leftmost(child)
        end
      end
    end
    return nil
  end
end

--------------------------------------------------------------------------------
-- 索引树操作
--------------------------------------------------------------------------------

-- 构造索引 cell: interior 时带 4 字节子指针
local function make_index_cell(bt, interior, child, payload)
  local out = {}
  if interior then out[#out + 1] = s32(child) end
  put_varint(out, #payload)
  local localn = local_size(bt, #payload, false)
  if localn < #payload then
    local first = write_overflow(bt, payload, localn)
    out[#out + 1] = sub(payload, 1, localn)
    out[#out + 1] = s32(first)
  else
    out[#out + 1] = payload
  end
  return concat(out)
end

-- 索引下降: target 为值数组 (record 的列值)
-- 返回 path, 到达页, 位置, 是否精确命中
local function index_descend(bt, target)
  local pager = bt.pager
  local path = {}
  local pageno = bt.root
  while true do
    local pg = pager:get_page(pageno)
    local hoff = hdr_off(pageno)
    local ptype = byte(pg, hoff)
    local hlen = hdr_len(ptype)
    local ncells = pg_ncells(pg, hoff)
    local interior = is_interior(ptype)
    local lo, hi, idx = 1, ncells, ncells + 1
    local found = false
    while lo <= hi do
      local mid = floor((lo + hi) / 2)
      local pos = cell_off(pg, hoff, hlen, mid) + 1
      local cell = parse_index_cell(bt, pg, pos, interior)
      local c = record_compare(decode_record(cell.payload), target)
      if c == 0 then
        idx = mid; found = true; break
      elseif c < 0 then lo = mid + 1
      else idx = mid; hi = mid - 1 end
    end
    if found then
      return path, pageno, idx, true
    end
    if not interior then
      return path, pageno, idx, false
    end
    local child
    local via_cell = idx <= ncells
    if via_cell then
      child = get_u(pg, cell_off(pg, hoff, hlen, idx) + 1, 4)
    else
      child = get_u(pg, hoff + 8, 4)
    end
    local entry = { pageno = pageno, cellidx = idx, via_cell = via_cell }
    if via_cell then
      -- 记录原 cell 的 tail (用于上移)
      local pos = cell_off(pg, hoff, hlen, idx) + 1
      local len = cell_total_len(bt, pg, pos, PT_IINT)
      entry.old_tail = sub(pg, pos + 4, pos + len - 1)
    end
    path[#path + 1] = entry
    pageno = child
  end
end

-- 重建索引内部页 (cells = {{child=,tail=}})
local function rebuild_iint(bt, pageno, cells, rightmost)
  local pager = bt.pager
  init_page(bt, pageno, PT_IINT)
  local pg = pager:get_page(pageno)
  pg = pw32(pg, hdr_off(pageno) + 8, rightmost)
  pager:set_page(pageno, pg)
  for i = 1, #cells do
    if not page_insert_cell(bt, pageno, i, s32(cells[i].child) .. cells[i].tail) then
      return false
    end
  end
  return true
end



-- 索引: 全量重排
local index_first_entry -- 前置声明

-- 子树中最小条目: 返回 payload, 页号, cell 序号
function index_first_entry(bt, pageno)
  local pg = bt.pager:get_page(pageno)
  local hoff = hdr_off(pageno)
  local ptype = byte(pg, hoff)
  local hlen = hdr_len(ptype)
  local ncells = pg_ncells(pg, hoff)
  if ptype == PT_ILEAF then
    if ncells == 0 then return nil end
    local pos = cell_off(pg, hoff, hlen, 1) + 1
    return parse_index_cell(bt, pg, pos, false).payload, pageno, 1
  end
  if ptype == PT_IINT then
    if ncells > 0 then
      local pos = cell_off(pg, hoff, hlen, 1) + 1
      local cell = parse_index_cell(bt, pg, pos, true)
      local r = index_first_entry(bt, cell.child)
      if r then return r end
      return cell.payload, pageno, 1
    end
    return index_first_entry(bt, get_u(pg, hoff + 8, 4))
  end
  return nil
end

-- 子树中最大条目
function index_last_entry(bt, pageno)
  local pg = bt.pager:get_page(pageno)
  local hoff = hdr_off(pageno)
  local ptype = byte(pg, hoff)
  local hlen = hdr_len(ptype)
  local ncells = pg_ncells(pg, hoff)
  if ptype == PT_ILEAF then
    if ncells == 0 then return nil end
    local pos = cell_off(pg, hoff, hlen, ncells) + 1
    return parse_index_cell(bt, pg, pos, false).payload, pageno, ncells
  end
  if ptype == PT_IINT then
    local r = index_last_entry(bt, get_u(pg, hoff + 8, 4))
    if r then return r end
    if ncells > 0 then
      local pos = cell_off(pg, hoff, hlen, ncells) + 1
      return parse_index_cell(bt, pg, pos, true).payload, pageno, ncells
    end
  end
  return nil
end

function BTree:rebuild_index(payloads)
  -- payloads: 已按 record_compare 排序的 payload 列表
  local pager = self.pager
  self:drop()
  local usable = pager.usable
  local groups, cur, curbytes = {}, {}, 0
  for i = 1, #payloads do
    local cellstr = make_index_cell(self, false, nil, payloads[i])
    if #cur > 0 and 8 + (#cur + 1) * 2 + curbytes + #cellstr > usable then
      groups[#groups + 1] = cur; cur, curbytes = {}, 0
    end
    cur[#cur + 1] = cellstr
    curbytes = curbytes + #cellstr
    assert(8 + #cur * 2 + curbytes <= usable, "索引项太大, 单页放不下")
  end
  if #cur > 0 then groups[#groups + 1] = cur end
  if #groups == 0 then
    local root = pager:alloc_page()
    init_page(self, root, PT_ILEAF)
    self.root = root
    return
  end
  local leaves, divs = {}, {}
  for gi = 1, #groups do
    local p = pager:alloc_page()
    init_page(self, p, PT_ILEAF)
    local g = groups[gi]
    if gi < #groups then
      divs[gi] = g[#g] -- 上移 divider
      g = { unpack(g, 1, #g - 1) }
    end
    for j = 1, #g do
      assert(page_insert_cell(self, p, j, g[j]))
    end
    leaves[gi] = p
  end
  -- 自底向上
  local level_pages, level_divs = leaves, divs
  while #level_pages > 1 do
    local npages = {}
    local i = 1
    while i <= #level_pages do
      local maxc = floor(usable / 10)
      local cnt = min(maxc, #level_pages - i + 1)
      local p = pager:alloc_page()
      init_page(self, p, PT_IINT)
      local rm
      for j = 1, cnt do
        local idx = i + j - 1
        if j == cnt and idx == #level_pages then
          rm = level_pages[idx]
        else
          assert(page_insert_cell(self, p, j,
            s32(level_pages[idx]) .. level_divs[idx]))
        end
      end
      if not rm then rm = level_pages[i + cnt - 1] end
      local pgx = pager:get_page(p)
      pgx = pw32(pgx, hdr_off(p) + 8, rm)
      pager:set_page(p, pgx)
      npages[#npages + 1] = p
      i = i + cnt
    end
    -- 新层的 dividers = 原层每个内部页的"最大条目"; 但我们在建层时已把 divider 用于 cell,
    -- 层间 divider 需要各子树最大条目 — 用 index_last_entry 取
    local ndivs = {}
    for pi = 1, #npages do
      local r = index_last_entry(self, npages[pi])
      assert(r, "内部错误: 重排时子树为空")
      ndivs[pi] = r
    end
    level_pages, level_divs = npages, ndivs
  end
  self.root = level_pages[1]
  self.pager.roots[self] = self.root
end

function BTree:insert_index(payload)
  local recvals = decode_record(payload)
  local _, _, _, found = index_descend(self, recvals)
  if found then
    err(CONSTRAINT, "UNIQUE 约束失败")
  end
  local cellstr = make_index_cell(self, false, nil, payload)
  local path, pageno, idx = index_descend(self, recvals)
  if page_insert_cell(self, pageno, idx, cellstr) then return end
  -- 页满: 局部重排 (父页的所有子叶合并重分组)
  if #path == 0 then
    local payloads = {}
    for pl in self:iter_index() do payloads[#payloads + 1] = pl end
    local lo, hi, at = 1, #payloads, #payloads + 1
    while lo <= hi do
      local mid = floor((lo + hi) / 2)
      local c = record_compare(decode_record(payloads[mid]), recvals)
      if c < 0 then lo = mid + 1 else at = mid; hi = mid - 1 end
    end
    insert(payloads, at, payload)
    self:rebuild_index(payloads)
    return
  end
  local node = path[#path]
  local pg = self.pager:get_page(node.pageno)
  local hoff = hdr_off(node.pageno)
  local ncells = pg_ncells(pg, hoff)
  local children = {}
  for i = 1, ncells do
    local pos = cell_off(pg, hoff, 12, i) + 1
    children[i] = get_u(pg, pos, 4)
  end
  children[ncells + 1] = get_u(pg, hoff + 8, 4)
  local allcells = {}
  -- 中序收集: 叶ci条目 -> divider ci (位于叶ci与叶ci+1之间) -> ...
  for ci = 1, #children do
    local pageno2 = children[ci]
    local lpg = self.pager:get_page(pageno2)
    local lhoff = hdr_off(pageno2)
    local ln = pg_ncells(lpg, lhoff)
    for i = 1, ln do
      local pos = cell_off(lpg, lhoff, 8, i) + 1
      local cell = parse_index_cell(self, lpg, pos, false)
      allcells[#allcells + 1] = cell.payload
    end
    if ci < #children then
      local pos = cell_off(pg, hoff, 12, ci) + 1
      local cell = parse_index_cell(self, pg, pos, true)
      allcells[#allcells + 1] = cell.payload
    end
  end
  -- 二分插入
  local lo, hi, at = 1, #allcells, #allcells + 1
  while lo <= hi do
    local mid = floor((lo + hi) / 2)
    local c = record_compare(decode_record(allcells[mid]), recvals)
    if c < 0 then lo = mid + 1 else at = mid; hi = mid - 1 end
  end
  insert(allcells, at, payload)
  -- 重新分组: 每组末尾(除最后)上移 divider
  local usable = self.pager.usable
  local limit = floor(usable * 2 / 3)
  local groups, cur, curbytes = {}, {}, 0
  for i = 1, #allcells do
    local cs = make_index_cell(self, false, nil, allcells[i])
    if #cur > 0 and 8 + (#cur + 1) * 2 + curbytes + #cs > limit then
      groups[#groups + 1] = cur; cur, curbytes = {}, 0
    end
    cur[#cur + 1] = cs
    curbytes = curbytes + #cs
    assert(8 + #cur * 2 + curbytes <= usable, "索引项太大, 单页放不下")
  end
  if #cur > 0 then groups[#groups + 1] = cur end
  local k = #groups
  local pages, dividers = {}, {}
  for i = 1, k do
    local p = (i <= #children) and children[i] or self.pager:alloc_page()
    init_page(self, p, PT_ILEAF)
    local g = groups[i]
    if i < k then
      dividers[i] = g[#g]
      g = { unpack(g, 1, #g - 1) }
    end
    for j = 1, #g do
      assert(page_insert_cell(self, p, j, g[j]), "索引局部重排失败")
    end
    pages[i] = p
  end
  -- 释放多余子页
  for i = k + 1, #children do self.pager:free_page(children[i]) end
  -- 重建父页
  local rc = {}
  for i = 1, k - 1 do rc[i] = { child = pages[i], tail = dividers[i] } end
  if rebuild_iint(self, node.pageno, rc, pages[k]) then return end
  -- 父页放不下: 先释放本次新分配的页, 再全量重排兜底
  for i = #children + 1, k do self.pager:free_page(pages[i]) end
  local payloads = {}
  for pl in self:iter_index() do payloads[#payloads + 1] = pl end
  self:rebuild_index(payloads)
end
function BTree:delete_index(payload)
  local _, pageno, idx, found = index_descend(self, decode_record(payload))
  if not found then return false end
  local pg = self.pager:get_page(pageno)
  local hoff = hdr_off(pageno)
  local ptype = byte(pg, hoff)
  if ptype == PT_ILEAF then
    page_delete_cell(self, pageno, idx)
    return true
  end
  -- 命中内部节点: 收集全部条目, 删除目标, 全量重排 (简单且正确)
  local entries = {}
  local target = decode_record(payload)
  for pl in self:iter_index() do
    if record_compare(decode_record(pl), target) ~= 0 then
      entries[#entries + 1] = pl
    end
  end
  if #entries == 0 then
    self:drop()
    local root = self.pager:alloc_page()
    init_page(self, root, PT_ILEAF)
    self.root = root
    self.pager.roots[self] = root
    return true
  end
  -- 条目已按序 (iter 顺序), 直接全量重排
  -- 保存/恢复 root 相关状态由 rebuild_index 处理
  local saved_root = self.root
  self:rebuild_index(entries)
  return true
end

-- 前缀搜索: 返回已有索引记录 payload (含 rowid), 无则 nil
function BTree:search_index_prefix(keyvals)
  local _, pageno, idx, found = index_descend(self, keyvals)
  local pg = self.pager:get_page(pageno)
  local hoff = hdr_off(pageno)
  local ptype = byte(pg, hoff)
  local hlen = hdr_len(ptype)
  local ncells = pg_ncells(pg, hoff)
  if found then
    local pos = cell_off(pg, hoff, hlen, idx) + 1
    return parse_index_cell(self, pg, pos, is_interior(ptype)).payload
  end
  if ptype ~= PT_ILEAF or idx > ncells then return nil end
  local pos = cell_off(pg, hoff, hlen, idx) + 1
  local payload = parse_index_cell(self, pg, pos, false).payload
  local vals = decode_record(payload)
  for i = 1, #keyvals do
    if value_compare(vals[i], keyvals[i]) ~= 0 then return nil end
  end
  return payload
end

-- 索引遍历 (中序): () -> payload
function BTree:iter_index()
  local pager = self.pager
  local stack = {}
  local function push_leftmost(pageno)
    local p = pageno
    while true do
      local pg = pager:get_page(p)
      local hoff = hdr_off(p)
      local ptype = byte(pg, hoff)
      if ptype == PT_IINT then
        local ncells = pg_ncells(pg, hoff)
        if ncells > 0 then
          -- cell 1 的左子树即将在下方下钻, 帧从 "输出 cell 1 payload" 开始
          stack[#stack + 1] = { pageno = p, next_cell = 1, phase = 2 }
          local pos = cell_off(pg, hoff, 12, 1) + 1
          p = get_u(pg, pos, 4)
        else
          -- 空内部页: 不压栈, 直接下钻 rightmost
          p = get_u(pg, hoff + 8, 4)
        end
      else
        stack[#stack + 1] = { pageno = p, next_cell = 1, phase = 1 }
        return
      end
    end
  end
  push_leftmost(self.root)
  return function()
    while #stack > 0 do
      local top = stack[#stack]
      local pg = pager:get_page(top.pageno)
      local hoff = hdr_off(top.pageno)
      local ptype = byte(pg, hoff)
      local ncells = pg_ncells(pg, hoff)
      if ptype == PT_ILEAF then
        if top.next_cell <= ncells then
          local pos = cell_off(pg, hoff, 8, top.next_cell) + 1
          top.next_cell = top.next_cell + 1
          return parse_index_cell(self, pg, pos, false).payload
        end
        stack[#stack] = nil
      else
        if top.phase == 1 and top.next_cell <= ncells then
          local pos = cell_off(pg, hoff, 12, top.next_cell) + 1
          top.phase = 2
          push_leftmost(get_u(pg, pos, 4))
        elseif top.phase == 2 and top.next_cell <= ncells then
          local pos = cell_off(pg, hoff, 12, top.next_cell) + 1
          local payload = parse_index_cell(self, pg, pos, true).payload
          top.next_cell = top.next_cell + 1
          top.phase = 1
          return payload
        else
          local child = get_u(pg, hoff + 8, 4)
          stack[#stack] = nil
          push_leftmost(child)
        end
      end
    end
    return nil
  end
end

-- 建根页
function BTree:create_root()
  local pgno = self.pager:alloc_page()
  init_page(self, pgno, self.kind == "table" and PT_TLEAF or PT_ILEAF)
  self.root = pgno
  self.pager.roots[self] = pgno
  return pgno
end

-- 释放整棵树的所有页
function BTree:drop()
  local pager = self.pager
  local function cell_ovf(pg, hoff, hlen, i, ptype)
    local pos = cell_off(pg, hoff, hlen, i) + 1
    local p = pos
    if ptype == PT_TINT then return 0 end
    if ptype == PT_IINT then p = p + 4 end
    local psz, p2 = get_varint(pg, p)
    if ptype == PT_TLEAF then
      local _, p3 = get_varint(pg, p2) -- 跳过 rowid varint
      p2 = p3
    end
    local localn = local_size(self, psz, ptype == PT_TLEAF)
    if localn < psz then
      return get_u(pg, p2 + localn, 4)
    end
    return 0
  end
  -- 先收集全部页号与溢出链, 再统一释放 (避免释放过程中遍历被改写)
  local all_pages, seen, all_ovf = {}, {}, {}
  local function collect(pageno)
    if pageno < 1 or pageno > pager.n_pages then
      err(CORRUPT, "drop: 非法页号 " .. tostring(pageno))
    end
    if seen[pageno] then return end
    seen[pageno] = true
    all_pages[#all_pages + 1] = pageno
    local pg = pager:get_page(pageno)
    local hoff = hdr_off(pageno)
    local ptype = byte(pg, hoff)
    local hlen = hdr_len(ptype)
    local ncells = pg_ncells(pg, hoff)
    if is_interior(ptype) then
      for i = 1, ncells do
        local pos = cell_off(pg, hoff, hlen, i) + 1
        collect(get_u(pg, pos, 4))
      end
      collect(get_u(pg, hoff + 8, 4))
    end
    for i = 1, ncells do
      local ovf = cell_ovf(pg, hoff, hlen, i, ptype)
      if ovf ~= 0 then
        -- 收集溢出链
        local p = ovf
        while p ~= 0 do
          if p < 1 or p > pager.n_pages then
            err(CORRUPT, "drop: 非法溢出页号 " .. tostring(p))
          end
          all_ovf[#all_ovf + 1] = p
          local opg = pager:get_page(p)
          p = get_u(opg, 1, 4)
        end
      end
    end
  end
  collect(self.root)
  for i = #all_ovf, 1, -1 do pager:free_page(all_ovf[i]) end
  for i = #all_pages, 1, -1 do pager:free_page(all_pages[i]) end
end

-- 新数据库初始化: 页 1 = 空 sqlite_master 叶 + 完整文件头
function Pager:init_new()
  self.n_pages = 1
  self:set_page(1, rep("\0", self.page_size))
  -- 构造空叶 (type 13, content = page_size)
  local hoff = 101
  local head = char(PT_TLEAF) .. s16(0) .. s16(0) ..
               (self.page_size >= 65536 and s16(0) or s16(self.page_size)) .. char(0)
  local pg = sub(self:get_page(1), 1, 100) .. head .. rep("\0", self.page_size - 100 - #head)
  self:set_page(1, pg)
end

-- 扫描所有树可达页 (含溢出链)
function Pager:reachable_pages()
  local seen, list = {}, {}
  local oseen = {}
  local function walk(pageno)
    if pageno < 1 or pageno > self.n_pages or seen[pageno] then return end
    seen[pageno] = true
    list[#list + 1] = pageno
    local pg = self:get_page(pageno)
    local hoff = pageno == 1 and 101 or 1
    local ptype = byte(pg, hoff)
    local hlen = is_interior(ptype) and 12 or 8
    local ncells = pg_ncells(pg, hoff)
    if is_interior(ptype) then
      for i = 1, ncells do
        local pos = cell_off(pg, hoff, hlen, i) + 1
        walk(get_u(pg, pos, 4))
      end
      walk(get_u(pg, hoff + 8, 4))
    end
    for i = 1, ncells do
      local pos = cell_off(pg, hoff, hlen, i) + 1
      local p = pos
      if ptype == PT_IINT then p = p + 4 end
      local psz, p2 = get_varint(pg, p)
      if ptype == PT_TLEAF then
        local _, p3 = get_varint(pg, p2)
        p2 = p3
      end
      local localn = local_size_bt(self, psz, ptype == PT_TLEAF)
      if localn < psz then
        local ovp = get_u(pg, p2 + localn, 4)
        while ovp ~= 0 and ovp >= 1 and ovp <= self.n_pages and not oseen[ovp] do
          oseen[ovp] = true
          seen[ovp] = true
          list[#list + 1] = ovp
          local opg = self:get_page(ovp)
          ovp = get_u(opg, 1, 4)
        end
      end
    end
  end
  for _, root in pairs(self.roots) do
    if root >= 1 and root <= self.n_pages then walk(root) end
  end
  walk(1)
  return seen
end

-- 清扫孤儿页: 挂到 freelist
function Pager:sweep_orphans()
  local reach = self:reachable_pages()
  local flp = {}
  local pgno = self.freelist_head
  while pgno ~= 0 and pgno >= 1 and pgno <= self.n_pages do
    flp[pgno] = true
    local pg = self:get_page(pgno)
    local nxt = get_u(pg, 1, 4)
    local cnt = get_u(pg, 5, 4)
    for i = 1, cnt do
      local leaf = get_u(pg, 9 + (i - 1) * 4, 4)
      if leaf >= 1 and leaf <= self.n_pages then flp[leaf] = true end
    end
    pgno = nxt
  end
  for i = 1, self.n_pages do
    if not reach[i] and not flp[i] then
      self:free_page(i)
    end
  end
end


--------------------------------------------------------------------------------
-- [4] Schema — sqlite_master 管理
--------------------------------------------------------------------------------
-- sqlite_master(type, name, tbl_name, rootpage, sql)
-- 我们解析 CREATE TABLE 的列定义, 支持:
--   类型: INTEGER/INT/TEXT/REAL/FLOAT/DOUBLE/BLOB/NUMERIC/VARCHAR(n)/CHAR(n)
--   约束: PRIMARY KEY [ASC|DESC] [AUTOINCREMENT] / NOT NULL / UNIQUE / DEFAULT 值
--   表级: PRIMARY KEY(列...), UNIQUE(列...)

local SCHEMA_ROOT = 1
local MT_ROWID = "_rowid_"

local Schema = {}
Schema.__index = Schema

local function schema_new(pager)
  local self = setmetatable({}, Schema)
  self.pager = pager
  self.master = bt_new(pager, SCHEMA_ROOT, "table")
  self.tables = {}     -- name -> table def
  self.indexes = {}     -- name -> index def
  self.table_order = {} -- 建表顺序
  self:load()
  return self
end

-- 解析 CREATE TABLE 的列
local function parse_create_table(sql)
  -- 找到第一个 '(' 之后最后一个 ')' 之间的列定义
  local s = sql:find("%(")
  if not s then return nil end
  -- 匹配括号 (考虑嵌套)
  local depth, e = 0, nil
  for i = s, #sql do
    local c = sql:sub(i, i)
    if c == "(" then depth = depth + 1
    elseif c == ")" then
      depth = depth - 1
      if depth == 0 then e = i; break end
    end
  end
  if not e then return nil end
  local body = sql:sub(s + 1, e - 1)
  -- 按顶层逗号分割
  local defs, depth2, cur = {}, 0, ""
  for i = 1, #body do
    local c = body:sub(i, i)
    if c == "(" then depth2 = depth2 + 1 end
    if c == ")" then depth2 = depth2 - 1 end
    if c == "," and depth2 == 0 then
      defs[#defs + 1] = cur; cur = ""
    else
      cur = cur .. c
    end
  end
  if cur ~= "" then defs[#defs + 1] = cur end
  -- 解析每个定义
  local cols = {}
  local pk_cols = nil -- 表级 PRIMARY KEY (a, b)
  local uniqs = {}
  for _, d in ipairs(defs) do
    d = d:gsub("^%s+", ""):gsub("%s+$", "")
    local lower = d:lower()
    if lower:match("^primary%s+key") then
      -- 表级: PRIMARY KEY (a, b)
      local inner = d:match("%((.-)%)")
      pk_cols = {}
      for cname in inner:gmatch("[^,]+") do
        pk_cols[#pk_cols + 1] = cname:gsub("^%s+", ""):gsub("%s+$", ""):lower()
      end
    elseif lower:match("^unique") then
      local inner = d:match("%((.-)%)")
      local uq = {}
      for cname in inner:gmatch("[^,]+") do
        uq[#uq + 1] = cname:gsub("^%s+", ""):gsub("%s+$", ""):lower()
      end
      uniqs[#uniqs + 1] = uq
    elseif lower:match("^check") or lower:match("^foreign%s+key") or lower:match("^constraint") then
      -- 忽略 CHECK / FOREIGN KEY
    else
      -- 列定义: name type constraints...
      local name, rest = d:match("^%s*([%w_]+)[%s\"]*(.*)$")
      if name then
        name = name:gsub('^"', ''):gsub('"$', '')
        local col = {
          name = name:lower(),
          cid = #cols,
          type = "blob",
          notnull = false,
          dflt = nil,
          pk = false,
          autoinc = false,
        }
        rest = rest or ""
        -- 类型
        local m = rest:match("^%s*(%a[%w%s%(%)]*)")
        local typ = ""
        if m then
          -- 截断到约束关键词
          local cut = #rest
          for kw in ("PRIMARY NOT UNIQUE DEFAULT CHECK REFERENCES COLLATE"):gmatch("%S+") do
            local p = rest:upper():find("%f[%w]" .. kw .. "%f[%W]")
            if p and p < cut then cut = p end
          end
          typ = rest:sub(1, cut):gsub("^%s+", ""):gsub("%s+$", "")
        end
        local tl = typ:lower()
        if tl:match("int") then col.type = "integer"
        elseif tl:match("text") or tl:match("char") or tl:match("clob") then col.type = "text"
        elseif tl:match("real") or tl:match("floa") or tl:match("doub") then col.type = "real"
        elseif tl:match("blob") then col.type = "blob"
        else col.type = "numeric" end
        -- 约束
        local ul = rest:lower()
        if ul:find("primary%s+key") then col.pk = true end
        if ul:find("autoincrement") then col.autoinc = true end
        if ul:find("not%s+null") then col.notnull = true end
        local dflt = rest:match("[Dd][Ee][Ff][Aa][Uu][Ll][Tt]%s+([^,]+)$")
        if dflt then
          dflt = dflt:gsub("^%s+", ""):gsub("%s+$", "")
          if dflt:sub(1, 1) == "'" then
            col.dflt = dflt:match("'(.*)'")
          elseif dflt:upper() == "NULL" then
            col.dflt = nil
          else
            col.dflt = tonumber(dflt) or dflt
          end
        end
        cols[#cols + 1] = col
      end
    end
  end
  if pk_cols then
    local byname = {}
    for _, c in ipairs(cols) do byname[c.name] = c end
    for _, n in ipairs(pk_cols) do
      if byname[n] then byname[n].pk = true end
    end
  end
  return cols, uniqs
end

function Schema:load()
  self.tables = {}
  self.indexes = {}
  self.table_order = {}
  local rows = {}
  for rowid, payload in self.master:iter_table() do
    rows[#rows + 1] = decode_record(payload)
  end
  table.sort(rows, function(a, b) return a[1] < b[1] end) -- 不重要, 顺序即 rowid
  local function handle(r)
    local typ, name, tbl_name, rootpage, sql = r[1], r[2], r[3], r[4], r[5]
    if typ == "table" then
      local cols, uniqs = parse_create_table(sql or "")
      self.tables[name:lower()] = {
        name = name, root = rootpage, sql = sql,
        cols = cols or {}, uniqs = uniqs or {},
      }
      self.table_order[#self.table_order + 1] = name:lower()
    elseif typ == "index" then
      local icols, tname, unique
      if sql then
        local collist
        tname, collist = sql:match("[Oo][Nn]%s+([%w_]+)%s*%((.-)%)")
        icols = {}
        if collist then
          for cn in collist:gmatch("[^,]+") do
            cn = cn:gsub("^%s+", ""):gsub("%s+$", ""):gsub("%s+[Aa][Ss][Cc]$", "")
            icols[#icols + 1] = cn:lower()
          end
        end
        unique = sql:upper():find("UNIQUE") ~= nil
      else
        -- sqlite_autoindex: 从表定义推导 UNIQUE 列 (按 autoindex 序号)
        tname = tbl_name and tbl_name:lower()
        unique = true
        icols = {}
        local tdef = self.tables[tname]
        if tdef and tdef.sql then
          local rawcols, uniqs = parse_create_table(tdef.sql)
          local sets = {}
          if rawcols then
            -- 列级 UNIQUE
            local body = tdef.sql:match("%((.*)%)")
            if body then
              local defs, d3, cur = {}, 0, ""
              for i = 1, #body do
                local ch = body:sub(i, i)
                if ch == "(" then d3 = d3 + 1 end
                if ch == ")" then d3 = d3 - 1 end
                if ch == "," and d3 == 0 then defs[#defs + 1] = cur; cur = ""
                else cur = cur .. ch end
              end
              if cur ~= "" then defs[#defs + 1] = cur end
              for _, dd in ipairs(defs) do
                local nm = dd:match("^%s*([%w_]+)")
                if nm and dd:upper():find("%f[%w]UNIQUE%f[%W]") then
                  sets[#sets + 1] = { nm:lower() }
                end
              end
            end
          end
          if uniqs then
            for _, uq in ipairs(uniqs) do sets[#sets + 1] = uq end
          end
          -- autoindex_N → 第 N 个
          local n = tonumber(name:match("_(%d+)$")) or 1
          if sets[n] then icols = sets[n] end
        end
      end
      self.indexes[name:lower()] = {
        name = name, table = tname, root = rootpage,
        sql = sql, cols = icols, unique = unique,
      }
    end
  end
  -- 先表后索引 (autoindex 推导需要表定义)
  for _, r in ipairs(rows) do
    if r[1] == "table" then handle(r) end
  end
  for _, r in ipairs(rows) do
    if r[1] ~= "table" then handle(r) end
  end
end

-- 应用 3 比较规则 (SQL 类型亲和性)
local function affinity_apply(col, v)
  if v == nil then return nil end
  if type(v) == "number" then return v end
  if type(v) == "string" then
    local aff = col.type
    if aff == "integer" or aff == "real" or aff == "numeric" then
      local n = tonumber(v)
      if n then
        if aff == "integer" and n == floor(n) and abs(n) < TWO63 then return n end
        if aff ~= "integer" then return n end
        return n
      end
      return v
    end
    return v
  end
  return v -- blob
end

function Schema:find_table(name)
  return self.tables[name:lower()]
end

function Schema:find_index(name)
  return self.indexes[name:lower()]
end

-- 表的索引列表
function Schema:table_indexes(tname)
  local out = {}
  for _, idx in pairs(self.indexes) do
    if idx.table == tname:lower() then out[#out + 1] = idx end
  end
  return out
end

-- 整数主键列 (rowid 别名)
function Schema:ipk_col(tdef)
  if #tdef.cols == 1 and tdef.cols[1].pk and tdef.cols[1].type == "integer" then
    return tdef.cols[1]
  end
  for _, c in ipairs(tdef.cols) do
    if c.pk and c.type == "integer" then return c end
  end
  return nil
end

--------------------------------------------------------------------------------
-- [5] Lexer — SQL 词法
--------------------------------------------------------------------------------

local Lexer = {}
Lexer.__index = Lexer

local KW = {}
for _, w in ipairs({
  "select", "from", "where", "group", "by", "order", "having", "limit", "offset",
  "insert", "into", "values", "update", "set", "delete", "create", "table",
  "index", "unique", "drop", "and", "or", "not", "null", "is", "in", "like",
  "between", "as", "join", "inner", "left", "outer", "cross", "on", "asc",
  "desc", "distinct", "all", "case", "when", "then", "else", "end", "cast",
  "exists", "collate", "primary", "key", "autoincrement", "default", "check",
  "references", "foreign", "constraint", "if", "begin", "commit", "rollback",
  "transaction", "conflict", "abort", "fail", "ignore", "replace", "glob",
  "union", "except", "intersect", "using", "natural", "escape", "isnull",
  "notnull", "view", "trigger", "temp", "temporary", "without", "rowid",
  "vacuum", "analyze", "pragma", "attach", "detach", "reindex",
}) do
  KW[w] = true
end

function Lexer.new(sql)
  return setmetatable({ s = sql, pos = 1 }, Lexer)
end

-- 返回 token: {t="id"/"kw"/"num"/"str"/"blob"/"op"/"eof", v=值, p=位置}
function Lexer:next()
  local s, p = self.s, self.pos
  -- 跳过空白与注释
  while true do
    while p <= #s and (s:sub(p, p):find("[%s \t\r\n]")) do p = p + 1 end
    if s:sub(p, p + 1) == "--" then
      p = s:find("\n", p) or (#s + 1)
    elseif s:sub(p, p + 1) == "/*" then
      local e2 = s:find("*/", p + 2)
      p = e2 and (e2 + 2) or (#s + 1)
    else
      break
    end
  end
  self.pos = p
  if p > #s then self.pos = p; return { t = "eof", v = nil, p = p } end
  local c = s:sub(p, p)
  -- 数字 (必须在标识符前: %w 含数字)
  if c:find("%d") or (c == "." and s:sub(p + 1, p + 1):find("%d")) then
    if s:sub(p, p + 1):lower() ~= "0x" then
      local e2 = p
      while e2 <= #s and s:sub(e2, e2):find("[%d%.eE]") do
        local nc = s:sub(e2, e2)
        if (nc == "e" or nc == "E") then
          local nn = s:sub(e2 + 1, e2 + 1)
          if nn == "+" or nn == "-" then e2 = e2 + 2 else e2 = e2 + 1 end
        else
          e2 = e2 + 1
        end
      end
      local numstr = s:sub(p, e2 - 1)
      self.pos = e2
      return { t = "num", v = tonumber(numstr), p = p }
    else
      local e2 = p + 2
      while e2 <= #s and s:sub(e2, e2):find("[%x]") do e2 = e2 + 1 end
      self.pos = e2
      return { t = "num", v = tonumber(s:sub(p + 2, e2 - 1), 16) or 0, p = p }
    end
  end
  -- 标识符 (排除纯数字已处理)
  if (c:find("[%a_]") or c == '"' or c == "`" or c == "[")
     or (c == "x" and s:sub(p + 1, p + 1) == "'") then
    local q = (c == '"' or c == "`" or c == "[") and c or nil
    if q then
      local qc = (q == "[") and "]" or q
      local e2 = s:find(qc, p + 1)
      if not e2 then err(ERROR, "未结束的标识符引号") end
      local word = s:sub(p + 1, e2 - 1)
      self.pos = e2 + 1
      return { t = "id", v = word, p = p }
    end
    local e2 = p
    while e2 <= #s and (s:sub(e2, e2):find("[%w_$]")) do e2 = e2 + 1 end
    local word = s:sub(p, e2 - 1)
    self.pos = e2
    local wl = word:lower()
    if KW[wl] then return { t = "kw", v = wl, p = p } end
    -- 命名参数 :name @name $name
    return { t = "id", v = word, p = p }
  end


  -- blob: x'..'
  if (c == "x" or c == "X") and s:sub(p + 1, p + 1) == "'" then
    local e2 = s:find("'", p + 2, true)
    if not e2 then err(ERROR, "未结束的 BLOB 字面量") end
    local hex = s:sub(p + 2, e2 - 1)
    if #hex % 2 ~= 0 then err(ERROR, "BLOB 字面量长度必须为偶数") end
    self.pos = e2 + 1
    local bytes = {}
    for i = 1, #hex, 2 do
      bytes[#bytes + 1] = char(tonumber(hex:sub(i, i + 1), 16))
    end
    return { t = "blob", v = blob(concat(bytes)), p = p }
  end
  -- 参数
  if c == "?" or c == ":" or c == "@" or c == "$" then
    local e2 = p + 1
    while e2 <= #s and s:sub(e2, e2):find("[%w_]") do e2 = e2 + 1 end
    local name = s:sub(p + 1, e2 - 1)
    self.pos = e2
    if c == "?" then
      if name == "" then
        self.qn = (self.qn or 0) + 1
        return { t = "param", v = self.qn, p = p }
      end
      return { t = "param", v = tonumber(name), p = p }
    end
    return { t = "param", v = name, p = p }
  end
  -- 字符串
  if c == "'" then
    local out = {}
    local q = p + 1
    while true do
      local e2 = s:find("'", q, true)
      if not e2 then err(ERROR, "未结束的字符串") end
      if s:sub(e2 + 1, e2 + 1) == "'" then
        out[#out + 1] = s:sub(q, e2) .. "'"
        q = e2 + 2
      else
        out[#out + 1] = s:sub(q, e2 - 1)
        self.pos = e2 + 1
        return { t = "str", v = concat(out), p = p }
      end
    end
  end
  -- blob: x'..'
  if (c == "x" or c == "X") and s:sub(p + 1, p + 1) == "'" then
    local e2 = s:find("'", p + 2, true)
    if not e2 then err(ERROR, "未结束的 BLOB 字面量") end
    local hex = s:sub(p + 2, e2 - 1)
    if #hex % 2 ~= 0 then err(ERROR, "BLOB 字面量长度必须为偶数") end
    self.pos = e2 + 1
    local bytes = {}
    for i = 1, #hex, 2 do
      bytes[#bytes + 1] = char(tonumber(hex:sub(i, i + 1), 16))
    end
    return { t = "blob", v = blob(concat(bytes)), p = p }
  end
  -- 参数
  if c == "?" or c == ":" or c == "@" or c == "$" then
    local e2 = p + 1
    while e2 <= #s and s:sub(e2, e2):find("[%w_]") do e2 = e2 + 1 end
    local name = s:sub(p + 1, e2 - 1)
    self.pos = e2
    if c == "?" then
      return { t = "param", v = tonumber(name) or true, p = p } -- ?N 或 ? (顺序)
    end
    return { t = "param", v = name, p = p }
  end
  -- 操作符
  local two = s:sub(p, p + 1)
  if two == "<=" or two == ">=" or two == "<>" or two == "!=" or two == "=="
     or two == "||" or two == "<<" or two == ">>" then
    self.pos = p + 2
    return { t = "op", v = two, p = p }
  end
  if c:find("[=<>%+%-%*/%%%(%)<>,;%.]") then
    self.pos = p + 1
    return { t = "op", v = c, p = p }
  end
  err(ERROR, ("无法识别的字符: %q (位置 %d)"):format(c, p))
end

-- 预读 (不推进)
function Lexer:peek()
  local save = self.pos
  local tk = self:next()
  self.pos = save
  return tk
end

--------------------------------------------------------------------------------
-- [6] Parser — SQL → AST
--------------------------------------------------------------------------------

local Parser = {}
Parser.__index = Parser

function Parser.new(sql)
  local p = setmetatable({ lx = Lexer.new(sql), sql = sql, tk = nil }, Parser)
  p:advance() -- 预读首 token
  return p
end

function Parser:advance()
  self.tk = self.lx:next()
  return self.tk
end

function Parser:expect_kw(word)
  local tk = self.tk
  if tk.t ~= "kw" or tk.v ~= word then
    err(ERROR, ("语法错误: 期望 %s, 得到 %s (位置 %d)")
      :format(word:upper(), tk.t == "eof" and "EOF" or tostring(tk.v), tk.p))
  end
  return self:advance()
end

function Parser:expect_op(op)
  local tk = self.tk
  if tk.t ~= "op" or tk.v ~= op then
    err(ERROR, ("语法错误: 期望 '%s', 得到 %s (位置 %d)")
      :format(op, tk.t == "eof" and "EOF" or tostring(tk.v), tk.p))
  end
  return self:advance()
end

function Parser:accept_kw(word)
  if self.tk.t == "kw" and self.tk.v == word then
    self:advance()
    return true
  end
  return false
end

function Parser:accept_op(op)
  if self.tk.t == "op" and self.tk.v == op then
    self:advance()
    return true
  end
  return false
end

function Parser:accept_id()
  if self.tk.t == "id" then
    local v = self.tk.v
    self:advance()
    return v
  end
  return nil
end

-- 解析表名 (可能是 db.table)
function Parser:parse_name()
  if self.tk.t ~= "id" then
    err(ERROR, "语法错误: 期望标识符, 得到 " .. tostring(self.tk.v))
  end
  local v = self.tk.v
  self:advance()
  -- 跳过 db. 前缀
  if self.tk.t == "op" and self.tk.v == "." and self.lx.s:sub(self.tk.p, #self.tk.v + self.tk.p - 1) == v then
    -- 不常见, 简化: 若形如 a.b 已被 lexer 合并 (含 .) 则无需处理
  end
  return v
end

-- ============ 表达式 ============
-- AST 节点:
--   {k="lit", v}
--   {k="col", name, src}      -- src: 数据源序号 (执行时绑定)
--   {k="param", v}
--   {k="bin", op, l, r}
--   {k="un", op, e}
--   {k="func", name, args, distinct}
--   {k="star"} / {k="tstar", t}
--   {k="in", e, list|select}
--   {k="between", e, lo, hi}
--   {k="like", e, pat, esc}
--   {k="isnull", e} / {k="notnull", e} / {k="is", e, e2}
--   {k="case", e, whens, els}
--   {k="cast", e, type}
--   {k="select", ...} (子查询)

function Parser:parse_expr()
  return self:parse_or()
end

function Parser:parse_or()
  local l = self:parse_and()
  while self.tk.t == "kw" and self.tk.v == "or" do
    self:advance()
    local r = self:parse_and()
    l = { k = "bin", op = "or", l = l, r = r }
  end
  return l
end

function Parser:parse_and()
  local l = self:parse_not()
  while self.tk.t == "kw" and self.tk.v == "and" do
    self:advance()
    local r = self:parse_not()
    l = { k = "bin", op = "and", l = l, r = r }
  end
  return l
end

function Parser:parse_not()
  if self.tk.t == "kw" and self.tk.v == "not" then
    self:advance()
    local e = self:parse_not()
    return { k = "un", op = "not", e = e }
  end
  return self:parse_cmp()
end

function Parser:parse_cmp()
  local l = self:parse_concat()
  while true do
    local tk = self.tk
    if tk.t == "op" and (tk.v == "=" or tk.v == "==" or tk.v == "!=" or tk.v == "<>"
        or tk.v == "<" or tk.v == "<=" or tk.v == ">" or tk.v == ">=") then
      self:advance()
      local op = (tk.v == "==") and "=" or (tk.v == "<>") and "!=" or tk.v
      local r = self:parse_concat()
      l = { k = "bin", op = op, l = l, r = r }
    elseif tk.t == "kw" and tk.v == "is" then
      self:advance()
      local neg = self:accept_kw("not")
      if self.tk.t == "kw" and self.tk.v == "null" then
        self:advance()
        l = { k = neg and "notnull" or "isnull", e = l }
      else
        local r = self:parse_concat()
        l = { k = "is", e = l, e2 = r, neg = neg }
      end
    elseif tk.t == "kw" and (tk.v == "isnull" or tk.v == "notnull") then
      local isn = tk.v == "isnull"
      self:advance()
      l = { k = isn and "isnull" or "notnull", e = l }
    elseif tk.t == "kw" and tk.v == "in" then
      self:advance()
      self:expect_op("(")
      if self.tk.t == "kw" and self.tk.v == "select" then
        local sub = self:parse_select()
        self:expect_op(")")
        l = { k = "in", e = l, select = sub }
      else
        local list = {}
        if not (self.tk.t == "op" and self.tk.v == ")") then
          list[1] = self:parse_expr()
          while self:accept_op(",") do
            list[#list + 1] = self:parse_expr()
          end
        end
        self:expect_op(")")
        l = { k = "in", e = l, list = list }
      end
    elseif tk.t == "kw" and tk.v == "like" then
      self:advance()
      local pat = self:parse_concat()
      local esc
      if self:accept_kw("escape") then
        esc = self:parse_concat()
      end
      l = { k = "like", e = l, pat = pat, esc = esc }
    elseif tk.t == "kw" and tk.v == "glob" then
      self:advance()
      local pat = self:parse_concat()
      l = { k = "like", e = l, pat = pat, esc = esc, glob = true }
    elseif tk.t == "kw" and tk.v == "between" then
      self:advance()
      local lo = self:parse_concat()
      self:expect_kw("and")
      local hi = self:parse_concat()
      l = { k = "between", e = l, lo = lo, hi = hi }
    else
      break
    end
  end
  return l
end

function Parser:parse_concat()
  local l = self:parse_add()
  while self.tk.t == "op" and self.tk.v == "||" do
    self:advance()
    local r = self:parse_add()
    l = { k = "bin", op = "||", l = l, r = r }
  end
  return l
end

function Parser:parse_add()
  local l = self:parse_mul()
  while self.tk.t == "op" and (self.tk.v == "+" or self.tk.v == "-") do
    local op = self.tk.v
    self:advance()
    local r = self:parse_mul()
    l = { k = "bin", op = op, l = l, r = r }
  end
  return l
end

function Parser:parse_mul()
  local l = self:parse_unary()
  while self.tk.t == "op" and (self.tk.v == "*" or self.tk.v == "/" or self.tk.v == "%") do
    local op = self.tk.v
    self:advance()
    local r = self:parse_unary()
    l = { k = "bin", op = op, l = l, r = r }
  end
  return l
end

function Parser:parse_unary()
  if self.tk.t == "op" and (self.tk.v == "-" or self.tk.v == "+" or self.tk.v == "~") then
    local op = self.tk.v
    self:advance()
    local e = self:parse_unary()
    if op == "+" then return e end
    return { k = "un", op = op, e = e }
  end
  if self.tk.t == "kw" and self.tk.v == "not" then
    self:advance()
    return { k = "un", op = "not", e = self:parse_unary() }
  end
  return self:parse_primary()
end

function Parser:parse_primary()
  local tk = self.tk
  if tk.t == "num" then
    self:advance()
    return { k = "lit", v = tk.v }
  elseif tk.t == "str" then
    self:advance()
    return { k = "lit", v = tk.v }
  elseif tk.t == "blob" then
    self:advance()
    return { k = "lit", v = tk.v }
  elseif tk.t == "param" then
    self:advance()
    return { k = "param", v = tk.v }
  elseif tk.t == "kw" and tk.v == "null" then
    self:advance()
    return { k = "lit", v = nil }
  elseif tk.t == "kw" and (tk.v == "true" or tk.v == "false") then
    -- SQLite 3.23+ 认 true/false
    self:advance()
    return { k = "lit", v = (tk.v == "true") and 1 or 0 }
  elseif tk.t == "kw" and tk.v == "cast" then
    self:advance()
    self:expect_op("(")
    local e = self:parse_expr()
    self:expect_kw("as")
    -- 类型名
    local ty = {}
    while self.tk.t == "id" or (self.tk.t == "kw" and not (self.tk.v == "end")) do
      ty[#ty + 1] = self.tk.v
      self:advance()
      if self.tk.t == "op" and self.tk.v == "(" then
        -- (n)
        self:advance()
        self:advance()
        self:expect_op(")")
      end
    end
    self:expect_op(")")
    return { k = "cast", e = e, type = concat(ty, " "):lower() }
  elseif tk.t == "kw" and tk.v == "case" then
    self:advance()
    local base
    if not (self.tk.t == "kw" and self.tk.v == "when") then
      base = self:parse_expr()
    end
    local whens = {}
    while self:accept_kw("when") do
      local cond = self:parse_expr()
      self:expect_kw("then")
      local res = self:parse_expr()
      whens[#whens + 1] = { cond = cond, res = res }
    end
    local els
    if self:accept_kw("else") then
      els = self:parse_expr()
    end
    self:expect_kw("end")
    return { k = "case", e = base, whens = whens, els = els }
  elseif tk.t == "kw" and tk.v == "exists" then
    self:advance()
    self:expect_op("(")
    local sub = self:parse_select()
    self:expect_op(")")
    return { k = "exists", select = sub }
  elseif tk.t == "op" and tk.v == "(" then
    self:advance()
    if self.tk.t == "kw" and self.tk.v == "select" then
      local sub = self:parse_select()
      self:expect_op(")")
      return { k = "subq", select = sub }
    end
    local e = self:parse_expr()
    -- 多列 (a, b)
    if self.tk.t == "op" and self.tk.v == "," then
      local list = { e }
      while self:accept_op(",") do
        list[#list + 1] = self:parse_expr()
      end
      self:expect_op(")")
      return { k = "row", list = list }
    end
    self:expect_op(")")
    return e
  elseif tk.t == "id" or (tk.t == "kw" and not KW_expr_stop[tk.v]) then
    -- 函数?
    local name = tk.v
    local pname = tk.p
    self:advance()
    if self.tk.t == "op" and self.tk.v == "(" then
      self:advance()
      local distinct = self:accept_kw("distinct") and true or nil
      local args = {}
      local star = false
      if self.tk.t == "op" and self.tk.v == "*" then
        self:advance()
        star = true
      elseif not (self.tk.t == "op" and self.tk.v == ")") then
        args[1] = self:parse_expr()
        while self:accept_op(",") do
          args[#args + 1] = self:parse_expr()
        end
      end
      self:expect_op(")")
      return { k = "func", name = name:lower(), args = args, distinct = distinct, star = star }
    end
    -- 列名: name / name.name (限定)
    if self.tk.t == "op" and self.tk.v == "." then
      self:advance()
      local n2 = self.tk.v
      self:advance()
      if self.tk.t == "op" and self.tk.v == "." then
        self:advance()
        local n3 = self.tk.v
        self:advance()
        return { k = "col", name = n3, src = name }
      end
      return { k = "col", name = n2, src = name }
    end
    if tk.t == "kw" then
      -- 关键词当列名 (如 left) — 仅在特定场景, 简化处理报错
      err(ERROR, ("语法错误: 意外的关键词 %s (位置 %d)"):format(name, pname))
    end
    return { k = "col", name = name }
  elseif tk.t == "op" and tk.v == "*" then
    self:advance()
    return { k = "star" }
  end
  err(ERROR, ("语法错误: 意外的 token %s (位置 %d)"):format(tostring(tk.v), tk.p))
end

KW_expr_stop = { ["end"] = true }

-- ============ SELECT ============
function Parser:parse_select()
  -- SELECT [distinct|all] 结果列 FROM ... [WHERE] [GROUP BY] [HAVING] [ORDER BY] [LIMIT]
  self:expect_kw("select")
  local node = { k = "select", cols = {}, from = nil, where = nil,
                 groupby = nil, having = nil, orderby = nil, limit = nil,
                 distinct = false }
  if self:accept_kw("distinct") then node.distinct = true
  else self:accept_kw("all") end
  -- 结果列
  repeat
    local e = self:parse_expr()
    local asname
    if self:accept_kw("as") then
      if self.tk.t == "id" or self.tk.t == "str" then
        asname = self.tk.v
        self:advance()
      else
        err(ERROR, "语法错误: AS 后需要别名")
      end
    elseif self.tk.t == "id" then
      -- 隐式别名 (仅标识符, 不吞关键词)
      asname = self.tk.v
      self:advance()
    end
    node.cols[#node.cols + 1] = { e = e, as = asname }
  until not self:accept_op(",")
  -- FROM
  if self:accept_kw("from") then
    node.from = self:parse_from()
  end
  if self:accept_kw("where") then
    node.where = self:parse_expr()
  end
  if self:accept_kw("group") then
    self:expect_kw("by")
    node.groupby = {}
    repeat
      node.groupby[#node.groupby + 1] = self:parse_expr()
    until not self:accept_op(",")
  end
  if self:accept_kw("having") then
    node.having = self:parse_expr()
  end
  if self:accept_kw("order") then
    self:expect_kw("by")
    node.orderby = {}
    repeat
      local e = self:parse_expr()
      local dir = "asc"
      if self:accept_kw("desc") then dir = "desc"
      else self:accept_kw("asc") end
      local nul
      if self:accept_kw("nulls") then
        if self:accept_kw("first") then nul = "first" else self:accept_kw("last"); nul = "last" end
      end
      node.orderby[#node.orderby + 1] = { e = e, dir = dir, nulls = nul }
    until not self:accept_op(",")
  end
  if self:accept_kw("limit") then
    node.limit = self:parse_expr()
    if self:accept_kw("offset") then
      node.limit_offset = self:parse_expr()
    elseif self:accept_op(",") then
      -- LIMIT off, n
      node.limit_offset = node.limit
      node.limit = self:parse_expr()
    end
  end
  return node
end

-- FROM: 表 / 子查询 / join
function Parser:parse_from()
  local function parse_one()
    if self.tk.t == "op" and self.tk.v == "(" then
      -- 可能是 (子查询) 或 (join)
      local save = self.lx.pos
      local saveTk = self.tk and self.tk.p
      self:advance() -- (
      if self.tk.t == "kw" and self.tk.v == "select" then
        local sub = self:parse_select()
        self:expect_op(")")
        local alias = self:accept_kw("as") and self:accept_id() or self:accept_id()
        return { k = "subqsrc", select = sub, alias = alias }
      end
      -- 回退解析 (join)
      self.lx.pos = save
      self.tk = nil
      -- 重新进入 (
      local j = self:parse_from()
      self:expect_op(")")
      return j
    end
    local name = self:parse_name()
    -- db.name
    if self.tk.t == "op" and self.tk.v == "." then
      self:advance()
      name = self:parse_name()
    end
    local alias
    if self:accept_kw("as") then
      alias = self:accept_id()
    else
      alias = self:accept_id()
    end
    return { k = "table", name = name, alias = alias }
  end
  local function parse_rest(left)
    while true do
      local tk = self.tk
      if tk.t == "kw" and (tk.v == "join" or tk.v == "inner" or tk.v == "left"
          or tk.v == "cross" or tk.v == "natural") then
        local jt = "inner"
        if tk.v == "left" then
          self:advance()
          self:accept_kw("outer")
          jt = "left"
        elseif tk.v == "cross" then
          self:advance()
          jt = "cross"
        elseif tk.v == "natural" then
          self:advance()
          jt = "inner"
        elseif tk.v == "inner" then
          self:advance()
        end
        self:expect_kw("join")
        local right = parse_one()
        local on
        if self:accept_kw("on") then
          on = self:parse_expr()
        elseif self:accept_kw("using") then
          self:expect_op("(")
          local cols = {}
          repeat
            cols[#cols + 1] = self.tk.v
            self:advance()
          until not self:accept_op(",")
          self:expect_op(")")
          on = { k = "using", cols = cols }
        end
        left = { k = "join", type = jt, l = left, r = right, on = on }
      elseif tk.t == "op" and tk.v == "," then
        self:advance()
        local right = parse_one()
        left = { k = "join", type = "cross", l = left, r = right, on = nil }
      else
        break
      end
    end
    return left
  end
  local first = parse_one()
  return parse_rest(first)
end

-- ============ 顶层语句 ============
function Parser:parse_stmt()
  local tk = self.tk
  if tk.t ~= "kw" then
    err(ERROR, "语法错误: 语句必须以关键词开头")
  end
  if tk.v == "select" then
    local node = self:parse_select() -- parse_select 自己 expect_kw("select")
    self:accept_op(";")
    return node
  end
  self:advance() -- 消费首 token (select 分支已自行处理)
  if tk.v == "begin" then
    self:accept_kw("transaction")
    self:accept_op(";")
    return { k = "begin" }
  elseif tk.v == "commit" then
    self:accept_kw("transaction")
    self:accept_kw("end")
    self:accept_op(";")
    return { k = "commit" }
  elseif tk.v == "rollback" then
    self:accept_kw("transaction")
    self:accept_op(";")
    return { k = "rollback" }
  elseif tk.v == "insert" or tk.v == "replace" then
    local replace = tk.v == "replace"
    self:accept_kw("or")
    local conflict
    if self.tk.t == "kw" and (self.tk.v == "replace" or self.tk.v == "abort"
        or self.tk.v == "fail" or self.tk.v == "ignore") then
      conflict = self.tk.v
      self:advance()
    end
    self:expect_kw("into")
    local name = self:parse_name()
    local cols
    if self.tk.t == "op" and self.tk.v == "(" then
      self:advance()
      cols = {}
      repeat
        cols[#cols + 1] = self.tk.v
        self:advance()
      until not self:accept_op(",")
      self:expect_op(")")
    end
    self:expect_kw("values")
    local rows = {}
    repeat
      self:expect_op("(")
      local vals = {}
      if not (self.tk.t == "op" and self.tk.v == ")") then
        vals[1] = self:parse_expr()
        while self:accept_op(",") do
          vals[#vals + 1] = self:parse_expr()
        end
      end
      self:expect_op(")")
      rows[#rows + 1] = vals
    until not self:accept_op(",")
    self:accept_op(";")
    return { k = "insert", table = name, cols = cols, rows = rows,
             replace = replace or conflict == "replace",
             ignore = conflict == "ignore" }
  elseif tk.v == "update" then
    local name = self:parse_name()
    self:expect_kw("set")
    local sets = {}
    repeat
      local cname = self.tk.v
      self:advance()
      self:expect_op("=")
      local e2 = self:parse_expr()
      sets[#sets + 1] = { col = cname, e = e2 }
    until not self:accept_op(",")
    local where
    if self:accept_kw("where") then
      where = self:parse_expr()
    end
    self:accept_op(";")
    return { k = "update", table = name, sets = sets, where = where }
  elseif tk.v == "delete" then
    self:expect_kw("from")
    local name = self:parse_name()
    local where
    if self:accept_kw("where") then
      where = self:parse_expr()
    end
    self:accept_op(";")
    return { k = "delete", table = name, where = where }
  elseif tk.v == "create" then
    local function skip_to_end()
      while self.tk.t ~= "eof" do self:advance() end
    end
    if self:accept_kw("table") then
      local rawsql = self.sql:gsub("%s*;?%s*$", "")
      if self:accept_kw("if") then
        self:expect_kw("not")
        self:expect_kw("exists")
      end
      local name = self:parse_name()
      skip_to_end()
      return { k = "create_table", name = name, sql = rawsql }
    end
    if self:accept_kw("unique") then
      self:accept_kw("index")
      local rawsql = self.sql:gsub("%s*;?%s*$", "")
      if self:accept_kw("if") then
        self:expect_kw("not")
        self:expect_kw("exists")
      end
      local name = self:parse_name()
      self:expect_kw("on")
      local tname = self:parse_name()
      skip_to_end()
      return { k = "create_index", name = name, table = tname, sql = rawsql, unique = true }
    end
    if self:accept_kw("index") then
      local rawsql = self.sql:gsub("%s*;?%s*$", "")
      if self:accept_kw("if") then
        self:expect_kw("not")
        self:expect_kw("exists")
      end
      local name = self:parse_name()
      self:expect_kw("on")
      local tname = self:parse_name()
      skip_to_end()
      return { k = "create_index", name = name, table = tname, sql = rawsql, unique = false }
    end
    err(ERROR, "语法错误: CREATE 后需要 TABLE/INDEX")
  elseif tk.v == "drop" then
    if self:accept_kw("table") then
      if self:accept_kw("if") then self:expect_kw("exists") end
      local name = self:parse_name()
      self:accept_op(";")
      return { k = "drop_table", name = name }
    end
    if self:accept_kw("index") then
      if self:accept_kw("if") then self:expect_kw("exists") end
      local name = self:parse_name()
      self:accept_op(";")
      return { k = "drop_index", name = name }
    end
    err(ERROR, "语法错误: DROP 后需要 TABLE/INDEX")
  elseif tk.v == "pragma" then
    while self.tk.t ~= "eof" do self:advance() end
    return { k = "pragma" }
  elseif tk.v == "vacuum" or tk.v == "analyze" then
    while self.tk.t ~= "eof" do self:advance() end
    return { k = "noop" }
  end
  err(ERROR, "不支持的语句: " .. tk.v:upper())
end

local SQLFuncs = {} -- 内置函数

-- 值的 SQL 文本化
local function sql_text(v)
  if v == nil then return "" end
  if is_blob(v) then return v[1] end
  if type(v) == "number" then
    if v == floor(v) and abs(v) < 1e15 then
      return format("%d", v)
    end
    return format("%.15g", v)
  end
  return tostring(v)
end

local function sql_num(v)
  if v == nil then return nil end
  if type(v) == "number" then return v end
  if type(v) == "string" then
    local s = v:match("^%s*([%+%-]?%d+%.?%d*[eE]?[%+%-]?%d*)%s*$")
    return s and tonumber(s) or nil
  end
  if is_blob(v) then return tonumber(v[1]) end
  return nil
end

-- 运算
local function sql_add(a, b)
  a, b = sql_num(a), sql_num(b)
  if a == nil or b == nil then return nil end
  return a + b
end
local function sql_arith(op, a, b)
  a, b = sql_num(a), sql_num(b)
  if a == nil or b == nil then return nil end
  if op == "+" then return a + b
  elseif op == "-" then return a - b
  elseif op == "*" then return a * b
  elseif op == "/" then
    if b == 0 then return nil end
    -- SQLite 整数除法在两整数时
    if type(a) == "number" and type(b) == "number" and floor(a) == a and floor(b) == b
       and abs(a) < TWO63 and abs(b) < TWO63 then
      local q = floor(a / b)
      if (a % b ~= 0) and ((a < 0) ~= (b < 0)) then q = q + 1 end
      return q
    end
    return a / b
  elseif op == "%" then
    if b == 0 then return nil end
    if floor(a) == a and floor(b) == b then
      return a - floor(a / b) * b
    end
    return a % b
  end
end

-- LIKE 匹配 (SQL: % _ , 默认无转义; 不区分 ASCII 大小写)
local function like_match(pat, s, esc, glob)
  -- 构建 Lua 模式
  local out = {}
  local i = 1
  local escch = esc and #esc > 0 and esc:sub(1, 1) or nil
  while i <= #pat do
    local c = pat:sub(i, i)
    if escch and c == escch and i < #pat then
      local n = pat:sub(i + 1, i + 1)
      out[#out + 1] = n:gsub("([%^%$%(%)%%%.%[%]%*%+%-%?])", "%%%1")
      i = i + 2
    elseif not glob and c == "%" then
      out[#out + 1] = ".*"
      i = i + 1
    elseif not glob and c == "_" then
      out[#out + 1] = "."
      i = i + 1
    elseif glob and c == "*" then
      out[#out + 1] = ".*"
      i = i + 1
    elseif glob and c == "?" then
      out[#out + 1] = "."
      i = i + 1
    else
      out[#out + 1] = c:gsub("([%^%$%(%)%%%.%[%]%*%+%-%?])", "%%%1")
      i = i + 1
    end
  end
  local luapat = "^" .. concat(out) .. "$"
  return s:find(luapat) ~= nil or s:lower():find(luapat:lower()) ~= nil
end

--------------------------------------------------------------------------------
-- 数据源 (执行上下文的一行)
-- row: { {vals=..., colmap=...}, ... } 每个源一个槽

local VM = {}
VM.__index = VM

local function vm_new(db)
  local self = setmetatable({}, VM)
  self.db = db
  self.sources = {} -- {name, tdef, bt, rowid, vals, colidx}
  return self
end

-- 找列: 返回 srcidx, colidx
function VM:findcol(name, srcname)
  name = name:lower()
  local found
  for si, src in ipairs(self.sources) do
    if not srcname or (src.alias or src.name):lower() == srcname:lower() then
      if src.rowid_alias == name then
        return si, -1 -- rowid
      end
      local ci = src.colidx and src.colidx[name]
      if ci then
        if found and found ~= si then
          err(ERROR, "歧义列名: " .. name)
        end
        found = si
        return si, ci
      end
    end
  end
  -- 找不到: 若无源 (如 SELECT 1+1) 报错
  err(ERROR, "没有这个列: " .. (srcname and (srcname .. ".") or "") .. name)
end

-- 求值
function VM:eval(e, row)
  local k = e.k
  if k == "lit" then return e.v
  elseif k == "param" then
    local v = self.params and self.params[e.v]
    return v
  elseif k == "col" then
    local si, ci = self:findcol(e.name, e.src)
    local src = self.sources[si]
    if ci == -1 then return row[si].rowid end
    if src.ipk_ci == ci then return row[si].rowid end -- INTEGER PRIMARY KEY = rowid
    return row[si].vals[ci + 1]
  elseif k == "bin" then
    local op = e.op
    if op == "and" then
      local l = self:eval(e.l, row)
      if l ~= nil and l ~= 0 and l ~= "" and l ~= false then
        local r = self:eval(e.r, row)
        if r ~= nil and r ~= 0 then return r else return false end
      elseif l == nil then
        local r = self:eval(e.r, row)
        if r == nil or r == 0 then return nil end
        return false
      else
        return false
      end
    elseif op == "or" then
      local l = self:eval(e.l, row)
      local truth = l ~= nil and l ~= 0
      if truth then return l end
      local r = self:eval(e.r, row)
      if r ~= nil and r ~= 0 then return r end
      if l == nil or r == nil then return nil end
      return false
    end
    local l = self:eval(e.l, row)
    local r = self:eval(e.r, row)
    if op == "||" then
      if l == nil or r == nil then return nil end
      return sql_text(l) .. sql_text(r)
    elseif op == "+" or op == "-" or op == "*" or op == "/" or op == "%" then
      return sql_arith(op, l, r)
    elseif op == "=" or op == "!=" or op == "<" or op == "<=" or op == ">" or op == ">=" then
      if l == nil or r == nil then return nil end
      local c = value_compare(l, r)
      -- 数值与文本比较: SQLite 用亲和性; 这里 value_compare 已分类
      if op == "=" then return c == 0
      elseif op == "!=" then return c ~= 0
      elseif op == "<" then return c < 0
      elseif op == "<=" then return c <= 0
      elseif op == ">" then return c > 0
      elseif op == ">=" then return c >= 0
      end
    end
    err(ERROR, "未知运算符: " .. op)
  elseif k == "un" then
    local v = self:eval(e.e, row)
    if e.op == "not" then
      if v == nil then return nil end
      return (v == 0) and 1 or 0
    elseif e.op == "-" then
      local n = sql_num(v)
      if n == nil then return nil end
      return -n
    elseif e.op == "~" then
      local n = sql_num(v)
      if n == nil then return nil end
      return bxor(floor(n), -1)
    end
  elseif k == "isnull" then
    return self:eval(e.e, row) == nil
  elseif k == "notnull" then
    return self:eval(e.e, row) ~= nil
  elseif k == "is" then
    local l = self:eval(e.e, row)
    local r = self:eval(e.e2, row)
    local same
    if l == nil and r == nil then same = true
    elseif l == nil or r == nil then same = false
    else same = value_compare(l, r) == 0 end
    return e.neg and (not same) or same
  elseif k == "in" then
    local v = self:eval(e.e, row)
    if v == nil then return nil end
    if e.select then
      local rows = self.db:exec_select_rows(e.select, self)
      for _, r in ipairs(rows) do
        if value_compare(v, r[1]) == 0 then return true end
      end
      return false
    end
    local anynull = false
    for _, le in ipairs(e.list) do
      local lv = self:eval(le, row)
      if lv == nil then anynull = true
      elseif value_compare(v, lv) == 0 then return true end
    end
    if anynull then return nil end
    return false
  elseif k == "between" then
    local v = self:eval(e.e, row)
    local lo = self:eval(e.lo, row)
    local hi = self:eval(e.hi, row)
    if v == nil or lo == nil or hi == nil then return nil end
    return value_compare(v, lo) >= 0 and value_compare(v, hi) <= 0
  elseif k == "like" then
    local v = self:eval(e.e, row)
    local pat = self:eval(e.pat, row)
    local esc = e.esc and self:eval(e.esc, row) or nil
    if v == nil or pat == nil then return nil end
    return like_match(sql_text(pat), sql_text(v), esc and sql_text(esc), e.glob)
  elseif k == "case" then
    if e.e then
      local base = self:eval(e.e, row)
      for _, w in ipairs(e.whens) do
        local c = self:eval(w.cond, row)
        if base ~= nil and c ~= nil and value_compare(base, c) == 0 then
          return self:eval(w.res, row)
        end
      end
    else
      for _, w in ipairs(e.whens) do
        local c = self:eval(w.cond, row)
        if c ~= nil and c ~= 0 and c ~= false then
          return self:eval(w.res, row)
        end
      end
    end
    return e.els and self:eval(e.els, row) or nil
  elseif k == "cast" then
    local v = self:eval(e.e, row)
    return self:cast_value(v, e.type)
  elseif k == "exists" then
    local rows = self.db:exec_select_rows(e.select, self)
    return #rows > 0
  elseif k == "subq" then
    local rows = self.db:exec_select_rows(e.select, self)
    if #rows == 0 then return nil end
    return rows[1][1]
  elseif k == "row" then
    local out = {}
    for i, le in ipairs(e.list) do
      out[i] = self:eval(le, row)
    end
    return out
  elseif k == "func" then
    return self:call_func(e, row)
  elseif k == "star" then
    err(ERROR, "不允许在此处使用 *")
  end
  err(ERROR, "未知表达式节点: " .. tostring(k))
end

function VM:cast_value(v, ty)
  if v == nil then return nil end
  ty = ty or ""
  if ty:find("int") then
    local n = sql_num(v)
    if n == nil then return 0 end
    return floor(n)
  elseif ty:find("real") or ty:find("floa") or ty:find("doub") then
    local n = sql_num(v)
    return n or 0.0
  elseif ty:find("text") or ty:find("char") or ty:find("clob") then
    return sql_text(v)
  elseif ty:find("blob") then
    if is_blob(v) then return v end
    return blob(sql_text(v))
  else -- numeric
    local n = sql_num(v)
    if n ~= nil then
      if n == floor(n) then return n end
      return n
    end
    return v
  end
end

-- 函数调用
function VM:call_func(e, row)
  local name = e.name
  -- 聚合
  local AGG = { count = true, sum = true, avg = true, min = true, max = true,
                total = true, group_concat = true, count_star = true }
  if AGG[name] and not self.no_aggregate then
    -- 聚合在行循环外处理; 此处不该到达 (exec_select 处理)
    err(ERROR, "聚合函数使用位置错误")
  end
  -- 用户自定义
  local uf = self.db.functions[name]
  if uf then
    local args = {}
    for i, a in ipairs(e.args) do args[i] = self:eval(a, row) end
    local r = uf.fn(unpack(args))
    if r == false then return 0 end
    if r == true then return 1 end
    return r
  end
  local bi = SQLFuncs[name]
  if not bi then
    err(ERROR, "没有这个函数: " .. name)
  end
  local args = {}
  for i, a in ipairs(e.args) do args[i] = self:eval(a, row) end
  return bi(self, args, e)
end

-- ============ 内置标量函数 ============

SQLFuncs["abs"] = function(vm, a)
  local n = sql_num(a[1])
  if n == nil then return nil end
  return abs(n)
end
SQLFuncs["length"] = function(vm, a)
  local v = a[1]
  if v == nil then return nil end
  if is_blob(v) then return #v[1] end
  return #tostring(v)
end
SQLFuncs["lower"] = function(vm, a)
  if a[1] == nil then return nil end
  return tostring(a[1]):lower()
end
SQLFuncs["upper"] = function(vm, a)
  if a[1] == nil then return nil end
  return tostring(a[1]):upper()
end
SQLFuncs["substr"] = function(vm, a)
  local v = a[1]
  if v == nil then return nil end
  local s = tostring(v)
  local st = sql_num(a[2]) or 1
  local ln = a[3] ~= nil and sql_num(a[3]) or nil
  local n = #s
  if st < 0 then st = n + st + 1 end
  if st < 1 then st = 1 end
  if ln == nil then return s:sub(st) end
  if ln < 0 then
    st = st + ln
    ln = -ln
    if st < 1 then st = 1; ln = ln - 1 end
  end
  return s:sub(st, st + ln - 1)
end
SQLFuncs["replace"] = function(vm, a)
  if a[1] == nil or a[2] == nil or a[3] == nil then return nil end
  return (tostring(a[1]):gsub(tostring(a[2]):gsub("%%", "%%%%"), function()
    return tostring(a[3])
  end))
end
SQLFuncs["trim"] = function(vm, a)
  if a[1] == nil then return nil end
  local s = tostring(a[1])
  local ch = a[2] and tostring(a[2]):gsub("%%", "%%%%") or "%s"
  return (s:gsub("^" .. ch .. "+", ""):gsub(ch .. "+$", ""))
end
SQLFuncs["ltrim"] = function(vm, a)
  if a[1] == nil then return nil end
  local s = tostring(a[1])
  local ch = a[2] and tostring(a[2]):gsub("%%", "%%%%") or "%s"
  return (s:gsub("^" .. ch .. "+", ""))
end
SQLFuncs["rtrim"] = function(vm, a)
  if a[1] == nil then return nil end
  local s = tostring(a[1])
  local ch = a[2] and tostring(a[2]):gsub("%%", "%%%%") or "%s"
  return (s:gsub(ch .. "+$", ""))
end
SQLFuncs["coalesce"] = function(vm, a)
  for _, v in ipairs(a) do
    if v ~= nil then return v end
  end
  return nil
end
SQLFuncs["ifnull"] = SQLFuncs["coalesce"]
SQLFuncs["nullif"] = function(vm, a)
  if a[1] ~= nil and a[2] ~= nil and value_compare(a[1], a[2]) == 0 then
    return nil
  end
  return a[1]
end
SQLFuncs["typeof"] = function(vm, a)
  local v = a[1]
  if v == nil then return "null" end
  if is_blob(v) then return "blob" end
  if type(v) == "number" then
    if floor(v) == v then return "integer" end
    return "real"
  end
  return "text"
end
SQLFuncs["round"] = function(vm, a)
  local n = sql_num(a[1])
  if n == nil then return nil end
  local d = a[2] and sql_num(a[2]) or 0
  local m = 10 ^ d
  return floor(n * m + 0.5) / m
end
SQLFuncs["hex"] = function(vm, a)
  local v = a[1]
  if v == nil then return "" end
  local s = is_blob(v) and v[1] or tostring(v)
  return (s:gsub(".", function(c) return format("%02X", byte(c)) end))
end
SQLFuncs["instr"] = function(vm, a)
  if a[1] == nil or a[2] == nil then return nil end
  return tostring(a[1]):find(tostring(a[2]), 1, true) or 0
end
SQLFuncs["printf"] = function(vm, a)
  -- 简化: 用 Lua format 的 %d %s %f
  if a[1] == nil then return nil end
  local ok, r = pcall(format, tostring(a[1]), select(2, unpack2(a)))
  return ok and r or tostring(a[1])
end
SQLFuncs["quote"] = function(vm, a)
  local v = a[1]
  if v == nil then return "NULL" end
  if type(v) == "number" then return sql_text(v) end
  if is_blob(v) then return "X'" .. SQLFuncs["hex"](vm, a) .. "'" end
  return "'" .. tostring(v):gsub("'", "''") .. "'"
end
SQLFuncs["random"] = function(vm, a)
  return math.random(-2147483648, 2147483647)
end
SQLFuncs["max_scalar"] = function(vm, a)
  local m
  for _, v in ipairs(a) do
    if v ~= nil then
      if m == nil or value_compare(v, m) > 0 then m = v end
    end
  end
  return m
end
SQLFuncs["min_scalar"] = function(vm, a)
  local m
  for _, v in ipairs(a) do
    if v ~= nil then
      if m == nil or value_compare(v, m) < 0 then m = v end
    end
  end
  return m
end
SQLFuncs["sqlite_version"] = function(vm, a)
  return "3.45.1"
end
SQLFuncs["char_func"] = function(vm, a)
  local out = {}
  for i, v in ipairs(a) do
    local n = sql_num(v)
    if n then out[#out + 1] = char(n % 256) end
  end
  return concat(out)
end
SQLFuncs["unicode"] = function(vm, a)
  if a[1] == nil then return nil end
  return tostring(a[1]):byte(1)
end
SQLFuncs["zeroblob"] = function(vm, a)
  local n = sql_num(a[1]) or 0
  return blob(rep("\0", max(0, floor(n))))
end

-- unpack 辅助 (Lua 5.1 兼容)
function unpack2(t)
  return unpack(t, 1, #t)
end

--------------------------------------------------------------------------------
-- [8] DB — 数据库对象 (lsqlite3 风格 API)
--------------------------------------------------------------------------------

local DB = {}
DB.__index = DB

local function db_open(fname)
  local self = setmetatable({}, DB)
  self.pager = Pager.open(fname)
  if self.pager.new_file then
    self.pager:init_new()
  end
  self.schema = schema_new(self.pager)
  self.functions = {}
  self.last_rowid = 0
  self.total_changes = 0
  self.in_txn = false
  return self
end

function DB:close()
  if self.pager then
    self.pager:close()
    self.pager = nil
  end
end

function DB:errmsg()
  return self._err or "not an error"
end

function DB:errcode()
  return self._errcode or OK
end

-- 执行 (可多条; 非查询返回 true)
function DB:exec(sql)
  local pos = 1
  while true do
    -- 跳过空白/分号
    while pos <= #sql and (sql:sub(pos, pos):find("[%s;]")) do pos = pos + 1 end
    if pos > #sql then break end
    -- 截取一条 (到分号, 但字符串内分号不算)
    local depth_str, endp = false, nil
    local i = pos
    while i <= #sql do
      local c = sql:sub(i, i)
      if c == "'" then depth_str = not depth_str
      elseif c == ";" and not depth_str then endp = i; break end
      i = i + 1
    end
    local stmt = (endp and sql:sub(pos, endp - 1) or sql:sub(pos)):gsub("^%s+", "")
    if #stmt > 0 then
      local ok, r = pcall(self.exec_one, self, stmt)
      if not ok then
        if type(r) == "table" then
          self._err, self._errcode = r.message, r.code
        else
          self._err, self._errcode = tostring(r), ERROR
        end
        return self._errcode
      end
    end
    if not endp then break end
    pos = endp + 1
  end
  self._err, self._errcode = "not an error", OK
  return OK
end

-- 执行单条语句
function DB:exec_one(sql)
  local p = Parser.new(sql)
  local node = p:parse_stmt()
  local k = node.k
  if k == "select" then
    local rows, cols = self:exec_select(node)
    if self.row_callback then
      for _, r in ipairs(rows) do self.row_callback(r, cols) end
    end
    return true
  elseif k == "insert" then
    return self:exec_insert(node)
  elseif k == "update" then
    return self:exec_update(node)
  elseif k == "delete" then
    return self:exec_delete(node)
  elseif k == "create_table" then
    return self:exec_create_table(node)
  elseif k == "create_index" then
    return self:exec_create_index(node)
  elseif k == "drop_table" then
    return self:exec_drop_table(node)
  elseif k == "drop_index" then
    return self:exec_drop_index(node)
  elseif k == "begin" then
    self.pager:begin_txn()
    self.in_txn = true
    return true
  elseif k == "commit" then
    if self.in_txn then
      self.pager:commit_txn()
      self.in_txn = false
    end
    return true
  elseif k == "rollback" then
    if self.in_txn then
      self.pager:rollback_txn()
      self.in_txn = false
      self.schema = schema_new(self.pager)
    end
    return true
  elseif k == "pragma" or k == "noop" then
    return true
  end
  err(ERROR, "未知语句类型: " .. tostring(k))
end

-- exec_one 包装: 统一在非事务时 flush
local _exec_one = DB.exec_one
function DB:exec_one(sql)
  local r = _exec_one(self, sql)
  if not self.in_txn and self.pager then self.pager:flush() end
  return r
end

-- ============ DDL ============

function DB:exec_create_table(node)
  local name = node.name
  if self.schema:find_table(name) then
    err(ERROR, "表已存在: " .. name)
  end
  -- 建新树
  local bt = bt_new(self.pager, 0, "table")
  bt:create_root()
  -- 写 master
  local sqlnorm = node.sql
  self.schema.master:insert_table(next_master_rowid(self),
    encode_record({ "table", name, name, bt.root, sqlnorm }))
  -- UNIQUE 约束列 → 创建 sqlite_autoindex (真 SQLite 行为, 保证文件互通)
  local rawcols, uniqs = parse_create_table(sqlnorm or "")
  local auto_n = 0
  local function make_auto_index(colnames)
    auto_n = auto_n + 1
    local tdef = { name = name, root = bt.root,
      cols = rawcols or {}, sql = sqlnorm }
    local ibt = bt_new(self.pager, 0, "index")
    ibt:create_root()
    -- 空 (表刚建); 记录到 master
    local iname = ("sqlite_autoindex_%s_%d"):format(name, auto_n)
    self.schema.master:insert_table(next_master_rowid(self),
      encode_record({ "index", iname, name, ibt.root, nil }))
  end
  if rawcols then
    for j, c in ipairs(rawcols) do
      -- 列级 UNIQUE → 单列自动索引 (重新扫描 SQL 列定义)
      local coldef = nil
      do
        local s2 = sqlnorm:find("%(")
        if s2 then
          local depth, e2 = 0, nil
          for i = s2, #sqlnorm do
            local ch = sqlnorm:sub(i, i)
            if ch == "(" then depth = depth + 1
            elseif ch == ")" then depth = depth - 1
              if depth == 0 then e2 = i; break end end
          end
          if e2 then
            local body = sqlnorm:sub(s2 + 1, e2 - 1)
            local defs, d3, cur = {}, 0, ""
            for i = 1, #body do
              local ch = body:sub(i, i)
              if ch == "(" then d3 = d3 + 1 end
              if ch == ")" then d3 = d3 - 1 end
              if ch == "," and d3 == 0 then defs[#defs + 1] = cur; cur = ""
              else cur = cur .. ch end
            end
            if cur ~= "" then defs[#defs + 1] = cur end
            for _, dd in ipairs(defs) do
              local nm = dd:match("^%s*([%w_]+)")
              if nm and nm:lower() == c.name and dd:upper():find("%f[%w]UNIQUE%f[%W]") then
                coldef = dd
              end
            end
          end
        end
      end
      if coldef then
        make_auto_index({ c.name })
      end
    end
    if uniqs then
      for _, uq in ipairs(uniqs) do
        make_auto_index(uq)
      end
    end
  end
  self.pager.schema_cookie = self.pager.schema_cookie + 1
  self.schema:load()
  return true
end

function DB:exec_create_index(node)
  if self.schema:find_index(node.name) then
    err(ERROR, "索引已存在: " .. node.name)
  end
  local tdef = self.schema:find_table(node.table)
  if not tdef then
    err(ERROR, "没有这个表: " .. node.table)
  end
  -- 解析列
  local collist, _ = node.sql:match("[Oo][Nn]%s+[%w_]+%s*%((.-)%)")
  local icols = {}
  for cn in collist:gmatch("[^,]+") do
    cn = cn:gsub("^%s+", ""):gsub("%s+$", ""):gsub("%s+[Aa][Ss][Cc]$", "")
    icols[#icols + 1] = cn:lower()
  end
  -- 建索引树: 遍历表, 插入 (cols..., rowid)
  local bt = bt_new(self.pager, 0, "index")
  bt:create_root()
  local tbt = bt_new(self.pager, tdef.root, "table")
  local colidx = {}
  for _, cn in ipairs(icols) do
    local ci
    for i, c in ipairs(tdef.cols) do
      if c.name == cn then ci = i - 1; break end
    end
    if not ci then err(ERROR, "没有这个列: " .. cn) end
    colidx[#colidx + 1] = ci
  end
  for rowid, payload in tbt:iter_table() do
    local vals = decode_record(payload)
    local key = {}
    for i, ci in ipairs(colidx) do key[i] = vals[ci + 1] end
    key[#key + 1] = rowid
    local ok, e = pcall(bt.insert_index, bt, encode_record(key))
    if not ok and node.unique then
      err(CONSTRAINT, "UNIQUE 约束失败: " .. node.name)
    end
  end
  self.schema.master:insert_table(next_master_rowid(self),
    encode_record({ "index", node.name, node.table, bt.root, node.sql }))
  self.pager.schema_cookie = self.pager.schema_cookie + 1
  self.schema:load()
  return true
end

function DB:exec_drop_table(node)
  local tdef = self.schema:find_table(node.name)
  if not tdef then
    err(ERROR, "没有这个表: " .. node.name)
  end
  -- 删关联索引
  for _, idx in ipairs(self.schema:table_indexes(node.name)) do
    local ibt = bt_new(self.pager, idx.root, "index")
    ibt:drop()
    self:delete_master_row(idx.name)
  end
  local tbt = bt_new(self.pager, tdef.root, "table")
  tbt:drop()
  self:delete_master_row(node.name)
  self.pager.schema_cookie = self.pager.schema_cookie + 1
  self.schema:load()
  return true
end

function DB:exec_drop_index(node)
  local idx = self.schema:find_index(node.name)
  if not idx then
    err(ERROR, "没有这个索引: " .. node.name)
  end
  local ibt = bt_new(self.pager, idx.root, "index")
  ibt:drop()
  self:delete_master_row(node.name)
  self.pager.schema_cookie = self.pager.schema_cookie + 1
  self.schema:load()
  return true
end

-- 更新 master 中某对象记录的 rootpage (树重排换根后调用)
function DB:update_master_root(name, newroot)
  name = name:lower()
  local m = self.schema.master
  for rowid, payload in m:iter_table() do
    local r = decode_record(payload)
    if r[2] and r[2]:lower() == name and r[4] ~= newroot then
      r[4] = newroot
      m:delete_table(rowid)
      m:insert_table(rowid, encode_record(r))
      return
    end
  end
end

-- master 的下一个 rowid
function next_master_rowid(db)
  local mr = db.schema.master:max_rowid() or 0
  return mr + 1
end

-- 删除 master 中的对象记录
function DB:delete_master_row(name)
  local m = self.schema.master
  local todel = {}
  for rowid, payload in m:iter_table() do
    local r = decode_record(payload)
    if r[2]:lower() == name:lower() then todel[#todel + 1] = rowid end
  end
  for _, rowid in ipairs(todel) do m:delete_table(rowid) end
end

-- 是否有覆盖该表任一列的唯一索引
function DB:_has_unique_index(tdef)
  for _, idx in ipairs(self.schema:table_indexes(tdef.name)) do
    if idx.unique then return true end
  end
  return false
end

-- 从 CREATE TABLE SQL 提取某列的定义子串
function DB:_coldef_of(sql, colname)
  if not sql then return nil end
  local s = sql:find("%(")
  if not s then return nil end
  local depth, e = 0, nil
  for i = s, #sql do
    local c = sql:sub(i, i)
    if c == "(" then depth = depth + 1
    elseif c == ")" then depth = depth - 1
      if depth == 0 then e = i; break end end
  end
  if not e then return nil end
  local body = sql:sub(s + 1, e - 1)
  local defs, d2, cur = {}, 0, ""
  for i = 1, #body do
    local c = body:sub(i, i)
    if c == "(" then d2 = d2 + 1 end
    if c == ")" then d2 = d2 - 1 end
    if c == "," and d2 == 0 then defs[#defs + 1] = cur; cur = ""
    else cur = cur .. c end
  end
  if cur ~= "" then defs[#defs + 1] = cur end
  for _, d in ipairs(defs) do
    local nm = d:match("^%s*([%w_]+)")
    if nm and nm:lower() == colname:lower() then return d end
  end
  return nil
end

-- 查找 UNIQUE 冲突的既有行 rowid
function DB:_find_unique_dup(tdef, colnames, vals, newrowid)
  local cis = {}
  for i, cn in ipairs(colnames) do
    for j, c in ipairs(tdef.cols) do
      if c.name == cn:lower() then cis[i] = j; break end
    end
    if not cis[i] then return nil end
  end
  -- 新值有 NULL 则不冲突
  for _, ci in ipairs(cis) do
    if vals[ci] == nil then return nil end
  end
  for rowid, rvals in self:table_rows(tdef) do
    if rowid ~= newrowid then
      local same = true
      for _, ci in ipairs(cis) do
        local a, b = rvals[ci], vals[ci]
        if a == nil or b == nil or value_compare(a, b) ~= 0 then
          same = false; break
        end
      end
      if same then return rowid end
    end
  end
  return nil
end

-- ============ DML ============

-- 行值 → record (处理 ipk 别名/默认值)
function DB:make_row_record(tdef, colnames, exprs, vm, params)
  local ipk = self.schema:ipk_col(tdef)
  local vals = {}
  local rowid
  -- 先算所有值
  local given = {}
  for i, cn in ipairs(colnames) do
    local ci
    for j, c in ipairs(tdef.cols) do
      if c.name == cn:lower() then ci = j; break end
    end
    if not ci then err(ERROR, "表 " .. tdef.name .. " 没有这个列: " .. cn) end
    given[ci] = exprs[i] and vm:eval(exprs[i], {}) or nil
  end
  -- 组装
  for j, c in ipairs(tdef.cols) do
    local v = given[j]
    if v == nil and ipk and c.name == ipk.name then
      -- rowid 别名, 留空 (NULL) 后面处理
      v = nil
    elseif v == nil and c.dflt ~= nil then
      v = c.dflt
    end
    if ipk and c.name == ipk.name then
      -- 存到 rowid
      if v ~= nil then
        rowid = sql_num(v)
        if rowid == nil or rowid ~= floor(rowid) then
          err(MISMATCH, "INTEGER PRIMARY KEY 必须是整数")
        end
      end
      v = nil -- ipk 列在 record 中存 NULL
    else
      v = affinity_apply(c, v)
    end
    vals[j] = v
  end
  return vals, rowid
end

function DB:exec_insert(node)
  local tdef = self.schema:find_table(node.table)
  if not tdef then err(ERROR, "没有这个表: " .. node.table) end
  local tbt = bt_new(self.pager, tdef.root, "table")
  local ipk = self.schema:ipk_col(tdef)
  -- 列名
  local colnames
  if node.cols then
    colnames = node.cols
  else
    colnames = {}
    for _, c in ipairs(tdef.cols) do colnames[#colnames + 1] = c.name end
  end
  local vm = vm_new(self)
  vm.params = node._params
  local autoinc = tdef.seq or 0
  for _, rowexprs in ipairs(node.rows) do
    if #rowexprs ~= #colnames then
      err(ERROR, ("%d 个值对应 %d 个列"):format(#rowexprs, #colnames))
    end
    local vals, rowid = self:make_row_record(tdef, colnames, rowexprs, vm)
    -- rowid 分配
    if rowid == nil and ipk then
      -- autoincrement 或 max+1
      if ipk.autoinc then
        local seq = tdef.seq or 0
        rowid = seq + 1
      else
        rowid = (tbt:max_rowid() or 0) + 1
      end
    elseif rowid == nil then
      rowid = (tbt:max_rowid() or 0) + 1
    end
    -- NOT NULL 检查
    for j, c in ipairs(tdef.cols) do
      if vals[j] == nil and c.notnull and not (ipk and c.name == ipk.name) then
        if node.ignore then goto continue end
        err(CONSTRAINT, "NOT NULL 约束失败: " .. tdef.name .. "." .. c.name)
      end
    end
    -- UNIQUE 约束检查 (列级 + 表级; 有唯一索引时由索引保证, 这里兜底)
    if not self:_has_unique_index(tdef) then
      local uqcols = {}
      for j, c in ipairs(tdef.cols) do
        if c.name:lower():match("unique") then end
      end
      -- 列级 UNIQUE: 从 SQL 判断
      local rawcols, uniqs = parse_create_table(tdef.sql or "")
      local check_sets = {}
      if rawcols then
        for j, c in ipairs(rawcols) do
          -- 单列 UNIQUE 检测: 需在 parse 时标记; 这里重新扫描 SQL
        end
      end
      -- 简化: 扫描 tdef.sql 列定义里的 UNIQUE
      for j, c in ipairs(tdef.cols) do
        local pat = c.name:gsub("%W", "%%%0") .. "%s+[^,()]*%f[%w][Uu][Nn][Ii][Qq][Uu][Ee]%f[%W]"
        local pat2 = c.name:gsub("%W", "%%%0") .. "%s+[%w%s]+,%s*[^)]*UNIQUE"
        -- 宽松: 在列定义子串中找 UNIQUE
        local coldef = self:_coldef_of(tdef.sql, c.name)
        if coldef and coldef:upper():find("%f[%w]UNIQUE%f[%W]") then
          check_sets[#check_sets + 1] = { c.name }
        end
      end
      if uniqs then
        for _, uq in ipairs(uniqs) do check_sets[#check_sets + 1] = uq end
      end
      for _, uq in ipairs(check_sets) do
        local dup = self:_find_unique_dup(tdef, uq, vals, rowid)
        if dup then
          if node.ignore then goto continue end
          if node.replace then
            -- 删除旧行
            tbt:delete_table(dup)
          else
            err(CONSTRAINT, ("UNIQUE 约束失败: %s.%s"):format(tdef.name, concat(uq, ",")))
          end
        end
      end
    end
    local payload = encode_record(vals, #tdef.cols)
    -- 唯一索引预检 (语句原子性: 全部检查通过后才写)
    do
      local conflict_rowid
      for _, idx in ipairs(self.schema:table_indexes(tdef.name)) do
        if idx.unique and #idx.cols > 0 then
          local key = {}
          local anynil = false
          for i, cn in ipairs(idx.cols) do
            for j, c in ipairs(tdef.cols) do
              if c.name == cn then key[i] = vals[j]; break end
            end
            if key[i] == nil then anynil = true; break end
          end
          if not anynil then
            local ibt = bt_new(self.pager, idx.root, "index")
            local hit = ibt:search_index_prefix(key)
            if hit then
              local hv = decode_record(hit)
              conflict_rowid = hv[#hv]
              if conflict_rowid == rowid then conflict_rowid = nil end
            end
          end
        end
        if conflict_rowid then
          if node.ignore then goto continue end
          if node.replace then
            -- 删冲突行
            local old_pl = tbt:search_table(conflict_rowid)
            if old_pl then
              self:update_indexes_delete(tdef, conflict_rowid, decode_record(old_pl))
              tbt:delete_table(conflict_rowid)
            end
          else
            err(CONSTRAINT, ("UNIQUE 约束失败: %s.%s"):format(tdef.name, table.concat(idx.cols, ",")))
          end
        end
      end
    end
    local ok, e = pcall(tbt.insert_table, tbt, rowid, payload)
    if not ok then
      if node.ignore then goto continue end
      if node.replace then
        -- 删除旧行 (含索引)
        local old_pl = tbt:search_table(rowid)
        if old_pl then
          self:update_indexes_delete(tdef, rowid, decode_record(old_pl))
          tbt:delete_table(rowid)
        end
        tbt:insert_table(rowid, payload)
      else
        if type(e) == "table" then error(e, 0) else error(tostring(e), 0) end
      end
    end
    if ipk and ipk.autoinc and rowid > (tdef.seq or 0) then
      tdef.seq = rowid
    end
    -- 维护索引
    self:update_indexes_insert(tdef, rowid, vals)
    self.last_rowid = rowid
    self.total_changes = self.total_changes + 1
    ::continue::
  end
  tdef.root = tbt.root -- 根可能因重排变化, 回写
  self:update_master_root(tdef.name, tdef.root)
  if not self.in_txn then self.pager:flush() end
  return true
end

-- 索引维护: 插入
function DB:update_indexes_insert(tdef, rowid, vals)
  for _, idx in ipairs(self.schema:table_indexes(tdef.name)) do
    local ibt = bt_new(self.pager, idx.root, "index")
    local key = {}
    for i, cn in ipairs(idx.cols) do
      for j, c in ipairs(tdef.cols) do
        if c.name == cn then key[i] = vals[j]; break end
      end
    end
    key[#idx.cols + 1] = rowid
    local ok, e = pcall(ibt.insert_index, ibt,
      encode_record(key, #idx.cols + 1))
    if ibt.root ~= idx.root then
      idx.root = ibt.root
      self:update_master_root(idx.name, ibt.root)
    end
    if not ok and idx.unique then
      if type(e) == "table" then error(e, 0) end
      error(tostring(e), 0)
    end
  end
end

-- 索引维护: 删除
function DB:update_indexes_delete(tdef, rowid, vals)
  for _, idx in ipairs(self.schema:table_indexes(tdef.name)) do
    local ibt = bt_new(self.pager, idx.root, "index")
    local key = {}
    for i, cn in ipairs(idx.cols) do
      for j, c in ipairs(tdef.cols) do
        if c.name == cn then key[i] = vals[j]; break end
      end
    end
    key[#idx.cols + 1] = rowid
    ibt:delete_index(encode_record(key, #idx.cols + 1))
    if ibt.root ~= idx.root then
      idx.root = ibt.root
      self:update_master_root(idx.name, ibt.root)
    end
  end
end

-- 表行遍历 (返回迭代器: rowid, vals)
function DB:table_rows(tdef)
  local tbt = bt_new(self.pager, tdef.root, "table")
  local iter = tbt:iter_table()
  return function()
    local rowid, payload = iter()
    if not rowid then return nil end
    return rowid, decode_record(payload)
  end
end

function DB:exec_update(node)
  local tdef = self.schema:find_table(node.table)
  if not tdef then err(ERROR, "没有这个表: " .. node.table) end
  local vm = vm_new(self)
  vm.params = node._params
  -- 单源
  vm.sources[1] = self:make_source(tdef, nil)
  local ipk = self.schema:ipk_col(tdef)
  -- 收集要更新的行
  local updates = {}
  for rowid, vals in self:table_rows(tdef) do
    local row = { { rowid = rowid, vals = vals } }
    if not node.where or self:truthy(vm, node.where, row) then
      updates[#updates + 1] = { rowid = rowid, vals = vals }
    end
  end
  local tbt = bt_new(self.pager, tdef.root, "table")
  for _, u in ipairs(updates) do
    local newvals = { unpack(u.vals, 1, #u.vals) }
    local row = { { rowid = u.rowid, vals = u.vals } }
    for _, s in ipairs(node.sets) do
      local ci
      for j, c in ipairs(tdef.cols) do
        if c.name == s.col:lower() then ci = j; break end
      end
      if not ci then err(ERROR, "没有这个列: " .. s.col) end
      local v = vm:eval(s.e, row)
      if ipk and tdef.cols[ci].name == ipk.name then
        err(ERROR, "不能修改 INTEGER PRIMARY KEY")
      end
      newvals[ci] = affinity_apply(tdef.cols[ci], v)
    end
    -- NOT NULL 检查
    for j, c in ipairs(tdef.cols) do
      if newvals[j] == nil and c.notnull and not (ipk and c.name == ipk.name) then
        err(CONSTRAINT, "NOT NULL 约束失败")
      end
    end
    self:update_indexes_delete(tdef, u.rowid, u.vals)
    tbt:delete_table(u.rowid)
    tbt:insert_table(u.rowid, encode_record(newvals, #tdef.cols))
    self:update_indexes_insert(tdef, u.rowid, newvals)
    self.total_changes = self.total_changes + 1
  end
  tdef.root = tbt.root
  if not self.in_txn then self.pager:flush() end
  return true
end

function DB:exec_delete(node)
  local tdef = self.schema:find_table(node.table)
  if not tdef then err(ERROR, "没有这个表: " .. node.table) end
  local vm = vm_new(self)
  vm.params = node._params
  vm.sources[1] = self:make_source(tdef, nil)
  local tbt = bt_new(self.pager, tdef.root, "table")
  -- 先收集要删除的行, 再删除 (遍历中删除会打乱迭代器)
  local todel = {}
  for rowid, vals in self:table_rows(tdef) do
    local row = { { rowid = rowid, vals = vals } }
    if not node.where or self:truthy(vm, node.where, row) then
      todel[#todel + 1] = { rowid = rowid, vals = vals }
    end
  end
  for _, d in ipairs(todel) do
    self:update_indexes_delete(tdef, d.rowid, d.vals)
    tbt:delete_table(d.rowid)
    self.total_changes = self.total_changes + 1
  end
  tdef.root = tbt.root
  tbt:prune_empty()
  tdef.root = tbt.root
  -- 根退化为 0-cell interior: 全量重建 (真 SQLite 根应有内容或是叶)
  do
    local rpg = self.pager:get_page(tdef.root)
    local rhoff = hdr_off(tdef.root)
    local rtype = byte(rpg, rhoff)
    if rtype == PT_TINT and pg_ncells(rpg, rhoff) == 0 then
      local entries = {}
      for rid, pl in tbt:iter_table() do
        entries[#entries + 1] = { rid, pl }
      end
      if #entries == 0 then
        init_page(tbt, tdef.root, PT_TLEAF)
      else
        tbt:rebuild_table(entries)
      end
      tdef.root = tbt.root
    end
  end
  self:update_master_root(tdef.name, tdef.root)
  if not self.in_txn then self.pager:flush() end
  return true
end

function DB:truthy(vm, e, row)
  local v = vm:eval(e, row)
  return v ~= nil and v ~= 0 and v ~= false
end

-- 构造数据源描述
function DB:make_source(tdef, alias, name)
  local colidx = {}
  for i, c in ipairs(tdef.cols) do colidx[c.name] = i - 1 end
  local ipk = self.schema:ipk_col(tdef)
  return {
    name = name or tdef.name, alias = alias, tdef = tdef,
    root = tdef.root, colidx = colidx, rowid_alias = "rowid",
    ipk_ci = ipk and (ipk.cid) or nil,
  }
end

-- ============ SELECT ============

-- 展开 FROM 为源列表 + 行迭代器
function DB:build_from(from, vm)
  if not from then
    return {}, function() return nil end
  end
  local function addsrc(f, vm)
    if f.k == "table" then
      local tdef = self.schema:find_table(f.name)
      if not tdef then err(ERROR, "没有这个表: " .. f.name) end
      local src = self:make_source(tdef, f.alias, f.name)
      vm.sources[#vm.sources + 1] = src
      local iter = self:table_rows(tdef)
      local si = #vm.sources
      return si, function()
        local rowid, vals = iter()
        if not rowid then return nil end
        return { [si] = { rowid = rowid, vals = vals } }
      end
    elseif f.k == "subqsrc" then
      local rows, cols = self:exec_select(f.select, vm)
      local si = #vm.sources + 1
      -- 建一个"匿名表" 源
      local colidx = {}
      for i, c in ipairs(cols) do colidx[c:lower()] = i - 1 end
      vm.sources[#vm.sources + 1] = {
        name = f.alias or ("#subq" .. si), alias = f.alias,
        tdef = nil, colidx = colidx, rowid_alias = "rowid",
      }
      local ri = 0
      return si, function()
        ri = ri + 1
        if ri > #rows then return nil end
        return { [si] = { rowid = ri, vals = rows[ri] } }
      end
    elseif f.k == "join" then
      local lsi, liter = addsrc(f.l, vm)
      local rsi, riter = addsrc(f.r, vm)
      local si_out -- 合并行
      -- join 迭代: 嵌套循环
      return nil, function()
        local lrow = liter()
        -- 实际需要保存迭代状态, 嵌套实现:
        error("内部错误: join 迭代器不应直接调用")
      end
    end
  end
  -- join 用递归生成器 (coroutine-free 嵌套循环展开)
  local function gen(f)
    if f.k == "table" then
      local tdef = self.schema:find_table(f.name)
      if not tdef then err(ERROR, "没有这个表: " .. f.name) end
      local src = self:make_source(tdef, f.alias, f.name)
      local si = #vm.sources + 1
      vm.sources[si] = src
      local function factory()
        local iter = self:table_rows(tdef)
        return function()
          local a, b = iter()
          if a == nil then return nil end
          return { [si] = { rowid = a, vals = b } }
        end
      end
      return si, "scan", factory
    elseif f.k == "subqsrc" then
      local si = #vm.sources + 1
      local rows0, cols0 = self:exec_select(f.select, vm)
      local colidx = {}
      for i, c in ipairs(cols0) do colidx[c:lower()] = i - 1 end
      vm.sources[si] = {
        name = f.alias or ("#subq" .. si), alias = f.alias,
        colidx = colidx, rowid_alias = "rowid",
      }
      local function factory()
        local ri = 0
        return function()
          ri = ri + 1
          if ri > #rows0 then return nil end
          return { [si] = { rowid = ri, vals = rows0[ri] } }
        end
      end
      return si, "rows", factory
    elseif f.k == "join" then
      local lsi, lkind, lfac = gen(f.l)
      local rsi, rkind, rfac = gen(f.r)
      return { lsi = lsi, rsi = rsi, lkind = lkind, lfac = lfac,
               rkind = rkind, rfac = rfac, on = f.on, vm = vm,
               jtype = f.type }, "join", nil
    end
  end
  local root_si, kind, nextf = gen(from)
  local function make_iter(si, kind, fac)
    if kind ~= "join" then
      local rowiter = fac() -- 一次性创建持久迭代器 (嵌套 join 时由工厂重建)
      return function()
        local row = rowiter()
        if row == nil then return nil end
        return row
      end
    end
    -- join: 左流持久, 右流按左行重开
    local J = si
    local liter = make_iter(J.lsi, J.lkind, J.lfac)
    local riter_cur = nil
    local lrow = nil
    local matched = false
    return function()
      while true do
        if lrow == nil then
          lrow = liter()
          if lrow == nil then return nil end
          riter_cur = make_iter(J.rsi, J.rkind, J.rfac)
          matched = false
        end
        local rrow = riter_cur()
        if rrow == nil then
          if J.jtype == "left" and not matched then
            local out = {}
            for k, v in pairs(lrow) do out[k] = v end
            out[J.rsi] = { rowid = nil, vals = {} }
            lrow = nil
            return out
          end
          lrow = nil
        else
          local out = {}
          for k, v in pairs(lrow) do out[k] = v end
          for k, v in pairs(rrow) do out[k] = v end
          if J.on == nil or self:truthy(J.vm, J.on, out) then
            matched = true
            return out
          end
        end
      end
    end
  end
  local iter = make_iter(root_si, kind, nextf)
  return vm.sources, iter
end

-- 执行 SELECT (供子查询)
function DB:exec_select_rows(node, parent_vm)
  local rows, cols = self:exec_select(node, parent_vm)
  return rows, cols
end

function DB:exec_select(node, parent_vm)
  local vm = vm_new(self)
  vm.params = parent_vm and parent_vm.params or node._params
  local sources, rowiter = self:build_from(node.from, vm)
  -- 结果列展开 (*)
  local outcols = {} -- {name, expr}
  for _, c in ipairs(node.cols) do
    if c.e.k == "star" then
      for si, src in ipairs(sources) do
        if src.tdef then
          for _, col in ipairs(src.tdef.cols) do
            outcols[#outcols + 1] = {
              name = col.name,
              expr = { k = "col", name = col.name, src = src.alias or src.name },
            }
          end
        else
          err(ERROR, "不能对子查询使用 *")
        end
      end
    elseif c.e.k == "col" and false then
      -- (不用)
    else
      local nm = c.as or (c.e.k == "col" and c.e.name) or self:expr_name(c.e)
      outcols[#outcols + 1] = { name = nm, expr = c.e }
    end
  end
  -- WHERE 过滤 + 收集
  local rows = {}
  for row in rowiter do
    if not node.where or self:truthy(vm, node.where, row) then
      rows[#rows + 1] = row
    end
  end
  -- GROUP BY / 聚合
  local has_agg = false
  local function scan_agg(e)
    if not e or type(e) ~= "table" then return end
    if e.k == "func" then
      local AGG = { count = true, sum = true, avg = true, min = true,
                    max = true, total = true, group_concat = true }
      if AGG[e.name] then has_agg = true; e.is_agg = true end
      for _, a in ipairs(e.args or {}) do scan_agg(a) end
      return
    end
    for _, kk in ipairs({ "l", "r", "e", "e2", "lo", "hi", "pat", "cond", "res", "els" }) do
      if e[kk] and type(e[kk]) == "table" then scan_agg(e[kk]) end
    end
    if e.whens then
      for _, w in ipairs(e.whens) do scan_agg(w.cond); scan_agg(w.res) end
    end
    if e.list then
      for _, x in ipairs(e.list) do scan_agg(x) end
    end
  end
  for _, c in ipairs(outcols) do scan_agg(c.expr) end
  if node.groupby then
    for _, g in ipairs(node.groupby) do scan_agg(g) end
  end
  if node.having then scan_agg(node.having) end

  -- HAVING/ORDER BY 中的输出别名替换为对应表达式
  local function subst_aliases(e)
    if not e or type(e) ~= "table" then return e end
    if e.k == "col" and not e.src and e.name then
      for _, c in ipairs(outcols) do
        if c.name and c.expr and c.expr.k == "func"
           and c.name:lower() == e.name:lower() then
          return c.expr
        end
      end
    end
    -- 递归处理已知子结构 (避免误入 whens 等非节点表)
    local function sub1(x)
      if type(x) ~= "table" then return x end
      if x.k then return subst_aliases(x) end
      return x -- 非节点 (如 whens 条目) 原样
    end
    local out = {}
    for k2, v in pairs(e) do
      out[k2] = sub1(v)
    end
    if e.whens then
      local nw = {}
      for i, w in ipairs(e.whens) do
        nw[i] = { cond = subst_aliases(w.cond), res = subst_aliases(w.res) }
      end
      out.whens = nw
    end
    if e.list then
      local nl = {}
      for i, x in ipairs(e.list) do nl[i] = sub1(x) end
      out.list = nl
    end
    if e.args then
      local na = {}
      for i, x in ipairs(e.args) do na[i] = sub1(x) end
      out.args = na
    end
    return out
  end
  if node.having then node.having = subst_aliases(node.having) end
  if node.orderby then
    for i, o in ipairs(node.orderby) do o.e = subst_aliases(o.e) end
  end
  local result_rows, result_cols, group_rows_list
  if has_agg or node.groupby then
    -- 分组
    local groups = {}
    local gorder = {}
    if node.groupby then
      local gkeys = {}
      for _, row in ipairs(rows) do
        local key = {}
        for i, g in ipairs(node.groupby) do
          key[i] = vm:eval(g, row)
        end
        local kk = concat(map_str(key), "\1")
        if not groups[kk] then
          groups[kk] = { rows = {} }
          gorder[#gorder + 1] = kk
        end
        local g = groups[kk]
        g.rows[#g.rows + 1] = row
      end
    else
      -- 无 GROUP BY 的聚合: 全表一组
      local g = { rows = rows }
      gorder[1] = "\0"
      groups["\0"] = g
    end
    -- HAVING + 计算组结果
    local gout = {}
    group_rows_list = {}
    for _, kk in ipairs(gorder) do
      local g = groups[kk]
      local grow = { __group_rows = g.rows }
      if not node.having or self:truthy_agg(vm, node.having, g.rows, grow) then
        local out = {}
        for ci, c in ipairs(outcols) do
          out[ci] = self:eval_out(vm, c.expr, g.rows, grow)
        end
        gout[#gout + 1] = out
        group_rows_list[#group_rows_list + 1] = g.rows
      end
    end
    result_rows = gout
    result_cols = {}
    for i, c in ipairs(outcols) do result_cols[i] = c.name end
  else
    -- 普通行
    local out = {}
    for _, row in ipairs(rows) do
      local r = {}
      for ci, c in ipairs(outcols) do
        r[ci] = vm:eval(c.expr, row)
      end
      out[#out + 1] = r
    end
    result_rows = out
    result_cols = {}
    for i, c in ipairs(outcols) do result_cols[i] = c.name end
    -- DISTINCT
    if node.distinct then
      local seen, dd = {}, {}
      for _, r in ipairs(out) do
        local kk = concat(map_str(r), "\1")
        if not seen[kk] then
          seen[kk] = true
          dd[#dd + 1] = r
        end
      end
      result_rows = dd
    end
  end
  -- ORDER BY (支持任意表达式: 按行重算)
  if node.orderby then
    local function sortkey_ri(i, o)
      if o.e.k == "lit" and type(o.e.v) == "number" and floor(o.e.v) == o.e.v then
        return result_rows[i][floor(o.e.v)]
      end
      if o.e.k == "col" then
        for ci, c in ipairs(outcols) do
          if not c.hidden and c.name:lower() == o.e.name:lower() then
            return result_rows[i][ci]
          end
        end
        if not (has_agg or node.groupby) and rows[i] then
          return vm:eval(o.e, rows[i])
        end
        if (has_agg or node.groupby) and group_rows_list and group_rows_list[i] then
          return vm:eval(o.e, group_rows_list[i][1] or {})
        end
        return nil
      end
      if not (has_agg or node.groupby) and rows[i] then
        return vm:eval(o.e, rows[i])
      end
      return nil
    end
    local keyrows = {}
    for i = 1, #result_rows do
      local ks = {}
      for oi, o in ipairs(node.orderby) do
        ks[oi] = sortkey_ri(i, o)
      end
      keyrows[i] = ks
    end
    local idx = {}
    for i = 1, #result_rows do idx[i] = i end
    sort(idx, function(a, b)
      for oi, o in ipairs(node.orderby) do
        local av, bv = keyrows[a][oi], keyrows[b][oi]
        if av == nil and bv == nil then goto nk end
        if av == nil then return o.dir == "asc"
        elseif bv == nil then return o.dir ~= "asc" end
        local c = value_compare(av, bv)
        if c ~= 0 then
          if o.dir == "asc" then return c < 0 else return c > 0 end
        end
        ::nk::
      end
      return false
    end)
    local sorted = {}
    for i, oi in ipairs(idx) do sorted[i] = result_rows[oi] end
    result_rows = sorted
  end

  -- LIMIT/OFFSET
  if node.limit then
    local lim = vm:eval(node.limit, {})
    local off = node.limit_offset and vm:eval(node.limit_offset, {}) or 0
    lim = sql_num(lim) or 0
    off = sql_num(off) or 0
    if off < 0 then off = 0 end
    local out = {}
    for i = off + 1, min(off + lim, #result_rows) do
      out[#out + 1] = result_rows[i]
    end
    result_rows = out
  end
  -- 去掉隐藏列
  local visible = {}
  for i, c in ipairs(outcols) do
    if not c.hidden then visible[#visible + 1] = i end
  end
  if #visible ~= #outcols then
    local out = {}
    for _, r in ipairs(result_rows) do
      local nr = {}
      for i, ci in ipairs(visible) do nr[i] = r[ci] end
      out[#out + 1] = nr
    end
    result_rows = out
    local nc = {}
    for i, ci in ipairs(visible) do nc[i] = result_cols[ci] end
    result_cols = nc
  end
  return result_rows, result_cols
end

-- 表达式输出名
function DB:expr_name(e)
  local k = e.k
  if k == "col" then return e.name end
  if k == "lit" then return sql_text(e.v) end
  if k == "func" then
    return e.name:upper() .. "(" .. #e.args .. "参数)"
  end
  return "expr"
end

-- 聚合上下文求值: 先把表达式里的聚合节点替换为计算值, 再普通求值
function DB:eval_out(vm, e, grows, grow)
  local function subst(node)
    if type(node) ~= "table" then return node end
    if node.k == "func" and node.is_agg then
      return { k = "lit", v = self:eval_agg(vm, node, grows) }
    end
    -- 递归复制替换
    local out = {}
    for k2, v in pairs(node) do
      if type(v) == "table" and v.k then
        out[k2] = subst(v)
      else
        out[k2] = v
      end
    end
    return out
  end
  local e2b = subst(e)
  return vm:eval(e2b, grows[1] or grow or {})
end

function DB:truthy_agg(vm, e, grows, grow)
  local v = self:eval_out(vm, e, grows, grow)
  return v ~= nil and v ~= 0 and v ~= false
end

-- 聚合求值
function DB:eval_agg(vm, e, grows)
  local name = e.name
  if name == "count" then
    if #e.args == 0 or e.star then
      return #grows
    end
    local n = 0
    for _, row in ipairs(grows) do
      local v = vm:eval(e.args[1], row)
      if v ~= nil then n = n + 1 end
    end
    return n
  elseif name == "sum" or name == "total" then
    local s, anyint = 0, true
    local seen = false
    for _, row in ipairs(grows) do
      local v = vm:eval(e.args[1], row)
      if v ~= nil then
        seen = true
        local n = sql_num(v)
        if n == nil then return name == "total" and 0.0 or nil end
        if floor(n) ~= n then anyint = false end
        s = s + n
      end
    end
    if not seen then return name == "total" and 0.0 or nil end
    return s
  elseif name == "avg" then
    local s, n = 0, 0
    for _, row in ipairs(grows) do
      local v = vm:eval(e.args[1], row)
      if v ~= nil then
        local num = sql_num(v)
        if num == nil then return nil end
        s = s + num
        n = n + 1
      end
    end
    if n == 0 then return nil end
    return s / n
  elseif name == "min" then
    local m
    for _, row in ipairs(grows) do
      local v = vm:eval(e.args[1], row)
      if v ~= nil then
        if m == nil or value_compare(v, m) < 0 then m = v end
      end
    end
    return m
  elseif name == "max" then
    local m
    for _, row in ipairs(grows) do
      local v = vm:eval(e.args[1], row)
      if v ~= nil then
        if m == nil or value_compare(v, m) > 0 then m = v end
      end
    end
    return m
  elseif name == "group_concat" then
    local sep = ","
    if e.args[2] then
      sep = sql_text(vm:eval(e.args[2], grows[1] or {}))
    end
    local parts = {}
    for _, row in ipairs(grows) do
      local v = vm:eval(e.args[1], row)
      if v ~= nil then parts[#parts + 1] = sql_text(v) end
    end
    if #parts == 0 then return nil end
    return concat(parts, sep)
  end
  err(ERROR, "未知聚合: " .. name)

end

function map_str(t)
  local out = {}
  for i, v in ipairs(t) do
    out[i] = v == nil and "\0" or (type(v) == "number" and tostring(v) or tostring(v))
  end
  return out
end

--------------------------------------------------------------------------------
-- [9] lsqlite3 兼容 API
--------------------------------------------------------------------------------

-- 错误码常量 (lsqlite3 风格)
local SQLITE = {
  OK = 0, ROW = 100, DONE = 101,
  ERROR = 1, INTERNAL = 2, PERM = 3, ABORT = 4, BUSY = 5, LOCKED = 6,
  NOMEM = 7, READONLY = 8, INTERRUPT = 9, IOERR = 10, CORRUPT = 11,
  NOTFOUND = 12, FULL = 13, CANTOPEN = 14, EMPTY = 15, SCHEMA = 16,
  TOOBIG = 18, CONSTRAINT = 19, MISMATCH = 20, MISUSE = 21,
}

-- Statement 对象
local Stmt = {}
Stmt.__index = Stmt

function Stmt:bind_values(...)
  self.binds = self.binds or {}
  local n = select("#", ...)
  for i = 1, n do
    self.binds[i] = select(i, ...)
  end
  self.seq = 1
  return SQLITE.OK
end

function Stmt:bind_names(t)
  self.named = t
  self.seq = 1
  return SQLITE.OK
end

function Stmt:bind(i, v)
  self.binds = self.binds or {}
  if v == false then v = 0 elseif v == true then v = 1 end
  self.binds[i] = v
  return SQLITE.OK
end

function Stmt:step()
  local node = self.ast
  local vm = vm_new(self.db)
  vm.params = self.binds or {}
  if self.named then
    for k, v in pairs(self.named) do vm.params[k] = v end
  end
  node._params = vm.params
  if node.k == "select" then
    local rows, cols = self.db:exec_select(node, vm)
    self._rows, self._cols = rows, cols
    self._ri = 1
    self.colnames = cols
    return SQLITE.ROW
  else
    local ok, e = pcall(self.db.exec_one, self.db, self._sql_for_exec, node)
    if not ok then
      if type(e) == "table" then
        self.db._err, self.db._errcode = e.message, e.code
      else
        self.db._err, self.db._errcode = tostring(e), ERROR
      end
      return self.db._errcode
    end
    return SQLITE.DONE
  end
end

-- 迭代结果
function Stmt:_cur()
  return self._rows and self._rows[self._ri]
end

function Stmt:get_value(i)
  local r = self:_cur()
  return r and r[i + 1]
end

function Stmt:get_values()
  local r = self:_cur()
  return r and unpack(r, 1, #r)
end

function Stmt:get_name(i)
  return self.colnames and self.colnames[i + 1]
end

function Stmt:columns()
  return self.colnames or {}
end

function Stmt:finalize()
  self.db = nil
  return SQLITE.OK
end

function Stmt:reset()
  self._ri = 0
  self._rows = nil
  return SQLITE.OK
end

-- DB 语句方法
function DB:prepare(sql)
  local p = Parser.new(sql)
  local node = p:parse_stmt()
  local stmt = setmetatable({
    db = self, ast = node, sql = sql, _sql_for_exec = sql,
  }, Stmt)
  return stmt
end

function DB:nrows(sql, params)
  local stmt = self:prepare(sql)
  if params then
    stmt.binds = {}
    for i, v in ipairs(params) do stmt.binds[i] = v end
  end
  local code = stmt:step()
  if code ~= SQLITE.ROW then
    stmt:finalize()
    error(self._err or "查询失败", 2)
  end
  local cols = stmt.colnames
  local ri = 0
  local rows = stmt._rows
  local function iter()
    ri = ri + 1
    if ri > #rows then return nil end
    local row = rows[ri]
    local t = {}
    for i, cn in ipairs(cols) do
      t[cn] = row[i]
      t[i] = row[i]
    end
    t._stmt = nil
    return t, ri
  end
  -- 注: stmt 生命周期延到迭代结束 (简化: 全量取出)
  return iter, nil, nil
end

function DB:rows(sql, params)
  local iter, s, var = self:nrows(sql, params)
  local function iter2()
    local t = iter()
    if t == nil then return nil end
    local n = 0
    for k in pairs(t) do
      if type(k) == "number" then n = max(n, k) end
    end
    return unpack(t, 1, n)
  end
  return iter2, s, var
end

function DB:urows(sql, params)
  return self:rows(sql, params)
end

function DB:exec_safe(sql)
  return self:exec(sql) == SQLITE.OK
end

function DB:create_function(name, nargs, fn)
  self.functions[name:lower()] = { n = nargs, fn = fn }
  return SQLITE.OK
end

function DB:last_insert_rowid()
  return self.last_rowid
end

function DB:changes()
  return self.total_changes
end

function DB:__close()
  self:close()
end

-- 模块导出
local M = {
  OK = SQLITE.OK, ROW = SQLITE.ROW, DONE = SQLITE.DONE,
  ERROR = SQLITE.ERROR, CONSTRAINT = SQLITE.CONSTRAINT,
  open = function(fname) return db_open(fname) end,
  open_memory = function()
    return db_open(nil) -- nil = 内存 (pager 不落盘)
  end,
  version = function() return "lsqlite3-compatible 1.0 (pure lua)" end,
  sqlite_version = function() return "3.45.1" end,
  errmsg = function(db) return db:errmsg() end,
}

-- 内存库支持: fname 为 nil 时用特殊 pager
do
  local orig_open = db_open
  db_open = function(fname)
    if fname == nil or fname == ":memory:" then
      local db = orig_open("__mem__")
      db.pager.is_memory = true
      -- 内存库: flush 什么都不写
      local orig_flush = db.pager.flush
      db.pager.flush = function(self2)
        self2.dirty = {}
        self2.snapshot = nil
      end
      db.pager.file = nil
      db.pager.new_file = false
      return db
    end
    return orig_open(fname)
  end
end

return M
