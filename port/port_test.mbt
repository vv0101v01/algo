// Blackbox tests for the port pipeline: assertions + property tests.

///|
test "map_type python table (assertions)" {
  assert_eq(@port.map_type("python", "int"), Some("Int"))
  assert_eq(@port.map_type("python", "float"), Some("Float"))
  assert_eq(@port.map_type("python", "bool"), Some("Bool"))
  assert_eq(@port.map_type("python", "str"), Some("String"))
  assert_eq(@port.map_type("python", "list[int]"), Some("Array[Int]"))
  assert_eq(
    @port.map_type("python", "List[list[str]]"),
    Some("Array[Array[String]]"),
  )
  assert_eq(@port.map_type("python", "Optional[str]"), Some("Option[String]"))
  assert_eq(@port.map_type("python", "int | None"), Some("Option[Int]"))
  assert_eq(
    @port.map_type("python", "dict[str, int]"),
    Some("Map[String, Int]"),
  )
  assert_eq(@port.map_type("python", "Custom"), None)
}

///|
test "map_type rust table (assertions)" {
  assert_eq(@port.map_type("rust", "i32"), Some("Int"))
  assert_eq(@port.map_type("rust", "usize"), Some("Int"))
  assert_eq(@port.map_type("rust", "f64"), Some("Float"))
  assert_eq(@port.map_type("rust", "&str"), Some("String"))
  assert_eq(@port.map_type("rust", "Vec<i32>"), Some("Array[Int]"))
  assert_eq(@port.map_type("rust", "Option<String>"), Some("Option[String]"))
  assert_eq(@port.map_type("rust", "HashMap<i32, i32>"), None)
}

///|
test "extract function signatures (assertions)" {
  let src = "def add(a: int, b: int = 1) -> int:\n  return a + b\n\nasync def fetch(url: str) -> None:\n  pass\n"
  let sigs = @port.extract_functions(src)
  assert_eq(sigs.length(), 2)
  assert_eq(sigs[0].name, "add")
  assert_eq(sigs[0].params.length(), 2)
  assert_eq(sigs[0].params[0].name, "a")
  assert_eq(sigs[0].params[0].ty, "int")
  assert_eq(sigs[0].params[1].ty, "int")
  assert_eq(sigs[0].ret, "int")
  assert_eq(sigs[0].lineno, 1)
  assert_eq(sigs[1].name, "fetch")
  assert_eq(sigs[1].ret, "None")
  assert_eq(@port.extract_functions("x = 1\nprint('hi')\n").length(), 0)
}

///|
test "extract tests and assertions (assertions)" {
  let src = "def test_add():\n  assert add(1, 2) == 3\n  assert add(0, 0) == 0\n\ndef helper():\n  return 1\n"
  let names = @port.extract_test_names(src)
  assert_eq(names.length(), 1)
  assert_eq(names[0], "test_add")
  assert_eq(@port.count_asserts(src), 2)
}

///|
test "full pipeline produces mapped skeleton (assertions)" {
  let src = "def add(a: int, b: int) -> int:\n  return a + b\n\ndef greet(name: str) -> str:\n  return 'hi ' + name\n"
  let r = @port.migrate(src)
  assert_eq(r.total, 2)
  assert_eq(r.mapped, 2)
  assert_eq(r.unmapped.length(), 0)
  assert_true(r.skeleton.contains("pub fn add(a : Int, b : Int) -> Int {"))
  assert_true(r.skeleton.contains("pub fn greet(name : String) -> String {"))
  assert_true(r.skeleton.contains("abort(\"尚未移植: add\")"))
  assert_true(r.skeleton.contains("TODO(port)"))
}

///|
test "unmapped types collected, Json placeholder (assertions)" {
  let src = "def f(x: Custom, y: int) -> Custom:\n  return x\n"
  let r = @port.migrate(src)
  assert_eq(r.total, 1)
  assert_eq(r.mapped, 0)
  assert_eq(r.unmapped.length(), 1)
  assert_eq(r.unmapped[0], "Custom")
  assert_true(r.skeleton.contains("x : Json"))
  assert_true(r.skeleton.contains("-> Json"))
}

///|
test "JSON migration report (assertions)" {
  let r = @port.migrate("def add(a: int) -> int:\n  return a\n")
  let j = @port.report_json(r)
  assert_true(
    j.has_prefix(
      "{\"total\": 1, \"mapped\": 1, \"unmapped\": [], \"functions\": [{\"name\": \"add\", \"line\": 1}]}",
    ),
  )
}

///|
test "property: successful type mappings are nonempty (quickcheck)" {
  @quickcheck.check((s : String) => {
    match @port.map_type("python", s) {
      Some(t) => !t.is_empty()
      None => true
    }
  })
}

///|
test "property: extracted line numbers are nondecreasing (quickcheck)" {
  @quickcheck.check((s : String) => {
    let sigs = @port.extract_functions(
      "def a() -> int:\n  return 1\ndef b() -> int:\n  return 2\n" + s,
    )
    let mut i = 1
    let mut ok = true
    for sg in sigs {
      if sg.lineno < i {
        ok = false
      }
      i = sg.lineno
    }
    ok
  })
}

///|
test "property: migrate total counts every signature (quickcheck)" {
  @quickcheck.check((s : String) => {
    let r = @port.migrate("def f(x: int) -> int:\n  return x\n" + s)
    r.total >= 1 && r.total == r.sigs.length() && r.mapped <= r.total
  })
}
