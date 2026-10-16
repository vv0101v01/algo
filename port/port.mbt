// 移植流水線（pipeline porting）底層演算法：
//   原始碼 → 抽取函式簽名/型別/測試 → 型別映射 → MoonBit 骨架 + 移植報告。
// 設計定位：只做底層演算法與資料結構（不實作 CLI 介面），
// 供上層 AI/CLI 驅動層呼叫：先生成骨架，再由 AI 填入主體。

///|
/// 一個被抽取出的函式簽名參數。
pub struct Param {
  /// 原始參數名。
  name : String
  /// 原始型別註記（無型別標註則為空字串）。
  ty : String
}

///|
/// 一個被抽取出的函式簽名。
pub struct FuncSig {
  /// 函式名。
  name : String
  /// 參數列表（依序）。
  params : Array[Param]
  /// 原始回傳型別（無標註則為空字串）。
  ret : String
  /// 原始碼行號（1-based）。
  lineno : Int32
}

///|
/// 移植報告：記錄映射覆蓋率與骨架產出。
pub struct MigrationReport {
  /// 抽取到的函式總數。
  total : Int32
  /// 所有型別皆成功映射的函式數。
  mapped : Int32
  /// 無法映射的原始型別（去重、依序）。
  unmapped : Array[String]
  /// 全部簽名。
  sigs : Array[FuncSig]
  /// 產生的 MoonBit 骨架原始碼。
  skeleton : String
}

///|
/// 型別映射（Python → MoonBit）。
/// 定理（映射保持外形）：`map("List[" T "]") = Array[map(T)]`，其餘基本型逐一對應；
/// 對未收錄型別回傳 `None`（報告層記入 unmapped，骨架層以 `Json` 佔位）。
fn map_type_python(t0 : String) -> String? {
  let t = t0.trim().to_owned()
  if t == "int" {
    Some("Int")
  } else if t == "float" {
    Some("Float")
  } else if t == "bool" {
    Some("Bool")
  } else if t == "str" || t == "bytes" {
    Some("String")
  } else if t == "None" {
    Some("Unit")
  } else if (t.has_prefix("List[") || t.has_prefix("list[")) &&
    t.has_suffix("]") {
    let inner = t[5:t.length() - 1].to_owned()
    match map_type_python(inner) {
      Some(x) => Some("Array[" + x + "]")
      None => None
    }
  } else if t.has_prefix("Optional[") && t.has_suffix("]") {
    let inner = t[9:t.length() - 1].to_owned()
    match map_type_python(inner) {
      Some(x) => Some("Option[" + x + "]")
      None => None
    }
  } else if t.has_suffix(" | None") {
    let inner = t[0:t.length() - 7].to_owned()
    match map_type_python(inner) {
      Some(x) => Some("Option[" + x + "]")
      None => None
    }
  } else if t.has_prefix("dict[") && t.has_suffix("]") {
    let inner = t[5:t.length() - 1].to_owned()
    let mut key = ""
    let mut val = ""
    let mut depth = 0
    let mut idx = 0
    let mut split_at = -1
    for c in inner.iter() {
      if c == '[' {
        depth = depth + 1
      } else if c == ']' {
        depth = depth - 1
      } else if c == ',' && depth == 0 && split_at < 0 {
        split_at = idx
      }
      idx = idx + 1
    }
    if split_at >= 0 {
      key = inner[0:split_at].to_owned()
      val = inner[split_at + 1:].to_owned()
      match (map_type_python(key), map_type_python(val)) {
        (Some(k), Some(v)) => Some("Map[" + k + ", " + v + "]")
        (_, _) => None
      }
    } else {
      None
    }
  } else {
    None
  }
}

///|
/// 型別映射（Rust → MoonBit）。
fn map_type_rust(t0 : String) -> String? {
  let t = t0.trim().to_owned()
  if t == "i8" ||
    t == "i16" ||
    t == "i32" ||
    t == "i64" ||
    t == "isize" ||
    t == "u8" ||
    t == "u16" ||
    t == "u32" ||
    t == "u64" ||
    t == "usize" {
    Some("Int")
  } else if t == "f32" || t == "f64" {
    Some("Float")
  } else if t == "bool" {
    Some("Bool")
  } else if t == "String" || t == "&str" || t == "str" {
    Some("String")
  } else if (t.has_prefix("Vec<") || t.has_prefix("&[")) &&
    (t.has_suffix(">") || t.has_suffix("]")) {
    let inner = if t.has_prefix("Vec<") {
      t[4:t.length() - 1].to_owned()
    } else {
      t[2:t.length() - 1].to_owned()
    }
    match map_type_rust(inner) {
      Some(x) => Some("Array[" + x + "]")
      None => None
    }
  } else if t.has_prefix("Option<") && t.has_suffix(">") {
    let inner = t[7:t.length() - 1].to_owned()
    match map_type_rust(inner) {
      Some(x) => Some("Option[" + x + "]")
      None => None
    }
  } else {
    None
  }
}

///|
/// 統一型別映射入口：`lang ∈ {"python","py","rust","rs"}`。
/// 定理（骨架良構）：`map_type(lang, t) == Some(u) ⇒ u` 為非空合法 MoonBit 型別外形；
/// 對 `List[T]`/`Vec<T>` 等複合型，外形成立當且僅當內層映射成功。
pub fn map_type(lang : String, t : String) -> String? {
  if lang == "rust" || lang == "rs" {
    map_type_rust(t)
  } else {
    map_type_python(t)
  }
}

///|
/// 解析參數清單字串 `"a: int, b: str = None"` → `Array[Param]`。
pub fn parse_params(src : String) -> Array[Param] {
  let out : Array[Param] = []
  if src.trim().is_empty() {
    return out
  }
  for seg in src.split(",") {
    let s0 = seg.trim().to_owned()
    if !s0.is_empty() {
      // 先剝預設值 `= ...`
      let no_def = match s0.find("=") {
        Some(eq) => s0[0:eq].to_owned().trim().to_owned()
        None => s0
      }
      // 再切型別註記 `name: ty`
      let p = match no_def.find(":") {
        Some(c) =>
          Param::{
            name: no_def[0:c].to_owned().trim().to_owned(),
            ty: no_def[c + 1:].to_owned().trim().to_owned(),
          }
        None => Param::{ name: no_def, ty: "", }
      }
      out.push(p)
    }
  }
  out
}

///|
/// 解析 `") -> int:"` 片段 → 回傳型別（無則 `""`）。
fn parse_ret(after : String) -> String {
  if after.has_prefix(" -> ") {
    let r = after[4:].to_owned().trim().to_owned()
    if r.has_suffix(":") {
      r[0:r.length() - 1].to_owned().trim().to_owned()
    } else {
      r
    }
  } else {
    ""
  }
}

///|
/// 逐行抽取函式簽名（支援 `def`/`async def`，行式解析、容忍預設值）。
/// 定理（抽取充分性）：每個以 `def name(...)` 起頭且左右括號配對出現於同一行的
/// 定義，恰好產生一個 `FuncSig`，其 `lineno` 為該行行號。
pub fn extract_functions(src : String) -> Array[FuncSig] {
  let out : Array[FuncSig] = []
  let mut lineno = 0
  for line in src.split("\n") {
    lineno = lineno + 1
    let t = line.trim().to_owned()
    let is_async = t.has_prefix("async def ")
    if t.has_prefix("def ") || is_async {
      let body = if is_async { t[10:].to_owned() } else { t[4:].to_owned() }
      match body.find("(") {
        Some(open) =>
          match body.find(")") {
            Some(close) =>
              if close > open {
                let name = body[0:open].to_owned().trim().to_owned()
                if !name.is_empty() && !name.contains(" ") {
                  let params_src = body[open + 1:close].to_owned()
                  let after = body[close + 1:].to_owned()
                  out.push(FuncSig::{
                    name,
                    params: parse_params(params_src),
                    ret: parse_ret(after),
                    lineno,
                  })
                }
              }
            None => ()
          }
        None => ()
      }
    }
  }
  out
}

///|
/// 抽取測試函式名（`def test_...` / `async def test_...`）。
pub fn extract_test_names(src : String) -> Array[String] {
  let out : Array[String] = []
  for line in src.split("\n") {
    let t = line.trim().to_owned()
    let is_async = t.has_prefix("async def ")
    if t.has_prefix("def ") || is_async {
      let body = if is_async { t[10:].to_owned() } else { t[4:].to_owned() }
      if body.has_prefix("test_") {
        match body.find("(") {
          Some(open) => {
            let name = body[0:open].to_owned().trim().to_owned()
            if !name.contains(" ") {
              out.push(name)
            }
          }
          None => ()
        }
      }
    }
  }
  out
}

///|
/// 統計以 `assert` 起頭的斷言行數（移植時須一併搬運的性質）。
pub fn count_asserts(src : String) -> Int32 {
  let mut n = 0
  for line in src.split("\n") {
    let t = line.trim().to_owned()
    if t.has_prefix("assert ") || t.has_prefix("assert(") {
      n = n + 1
    }
  }
  n
}

///|
/// 產生單一函式的 MoonBit 骨架（型別映射失敗以 `Json` 佔位、標註 TODO）。
pub fn generate_skeleton(lang : String, s : FuncSig) -> String {
  let sb = StringBuilder::StringBuilder(size_hint=256)
  sb.write(
    "/// 移植自原始碼第 " +
    s.lineno.to_string() +
    " 行：" +
    s.name +
    "\n",
  )
  sb.write("pub fn " + s.name + "(")
  let mut first = true
  for p in s.params {
    if !first {
      sb.write(", ")
    }
    first = false
    let ty = if p.ty == "" {
      "Json"
    } else {
      match map_type(lang, p.ty) {
        Some(x) => x
        None => "Json"
      }
    }
    sb.write(p.name + " : " + ty)
  }
  sb.write(")")
  if s.ret != "" {
    let r = match map_type(lang, s.ret) {
      Some(x) => x
      None => "Json"
    }
    sb.write(" -> " + r)
  }
  sb.write(
    " {\n  // TODO(port): 移植原始函式主體（簽名已映射，待 AI/人工填入）\n",
  )
  sb.write("  abort(\"尚未移植: " + s.name + "\")\n}\n")
  sb.to_string()
}

///|
/// 一鍵移植流水線：抽取 → 映射 → 骨架 + 報告。
/// 定理（覆蓋率）：`mapped ≤ total`；`unmapped` 不含任何已成功映射的型別；
/// `skeleton` 中骨架片段數 = `total`（每個函式恰一段 `pub fn`）。
pub fn migrate(src : String, lang~ : String = "python") -> MigrationReport {
  let sigs = extract_functions(src)
  let unmapped : Array[String] = []
  let mut mapped = 0
  let sb = StringBuilder::StringBuilder(size_hint=1024)
  for s in sigs {
    let mut all_ok = true
    for p in s.params {
      if p.ty != "" {
        match map_type(lang, p.ty) {
          Some(_) => ()
          None => {
            all_ok = false
            if !unmapped.contains(p.ty) {
              unmapped.push(p.ty)
            }
          }
        }
      }
    }
    if s.ret != "" {
      match map_type(lang, s.ret) {
        Some(_) => ()
        None => {
          all_ok = false
          if !unmapped.contains(s.ret) {
            unmapped.push(s.ret)
          }
        }
      }
    }
    if all_ok {
      mapped = mapped + 1
    }
    sb.write(generate_skeleton(lang, s))
  }
  MigrationReport::{
    total: sigs.length(),
    mapped,
    unmapped,
    sigs,
    skeleton: sb.to_string(),
  }
}

///|
/// 報告轉 JSON（最小轉義，供上層 CLI/AI 讀取）。
pub fn report_json(r : MigrationReport) -> String {
  let sb = StringBuilder::StringBuilder(size_hint=512)
  sb.write("{\"total\": " + r.total.to_string())
  sb.write(", \"mapped\": " + r.mapped.to_string())
  sb.write(", \"unmapped\": [")
  let mut i = 0
  for u in r.unmapped {
    if i > 0 {
      sb.write(", ")
    }
    sb.write(
      "\"" +
      u.replace(old="\\", new="\\\\").replace(old="\"", new="\\\"") +
      "\"",
    )
    i = i + 1
  }
  sb.write("], \"functions\": [")
  i = 0
  for s in r.sigs {
    if i > 0 {
      sb.write(", ")
    }
    sb.write(
      "{\"name\": \"" + s.name + "\", \"line\": " + s.lineno.to_string() + "}",
    )
    i = i + 1
  }
  sb.write("]}")
  sb.to_string()
}
