// Learn more about moon.mod configuration:
// https://docs.moonbitlang.com/en/latest/toolchain/moon/module.html
//
// To add a dependency, run this command in your terminal:
//   moon add moonbitlang/x
//
// Or manually declare it in `import`, for example:
// import {
//   "moonbitlang/x@0.4.6",
// }

name = "moon-algebra"

version = "0.1.0"

readme = "README.mbt.md"

repository = "https://github.com/vv0101v01/algo"

license = "Apache-2.0"

keywords = [
  "abstract-algebra",
  "ring-theory",
  "polynomial",
  "groebner",
  "algebraic-geometry",
  "scheme",
  "finite-field",
  "homotopy-type-theory",
  "code-migration",
]

preferred_target = "wasm"

description = "Abstract algebra, linear algebra, algebraic geometry and schemes over finite fields for MoonBit"

warnings = "-implicit_impl_as_method"
