///|
/// Localization `R_S` of a finite algebra at a multiplicatively closed set
/// `S ∋ 1`. Elements are fractions `a/s` with `(a,s) ~ (b,t)` iff
/// `∃c ∈ S: c·(a·t − b·s) = 0` (exact finite-ring criterion — no ring
/// elements are ever inverted inside `R`; pairs carry denominators).
pub(all) struct Localization {
  base : FinAlg
  s_set : Array[Array[Int32]] // canonical members of S (1 added, closed under ·)
  s_codes : Array[Int32]
  s_idx_of : Array[Int32] // element code → index in s_set (−1 if not in S)
  pair_num : Array[Int32] // pair id → numerator element code
  pair_den : Array[Int32] // pair id → denominator index into s_set
  pair_class : Array[Int32] // pair id → class id
  class_count : Int32
  class_pair : Array[Int32] // class id → representative pair id
  mul_code : Array[Int32] // flat N×N: code(x)·N + code(y) → code(x·y)
  add_code : Array[Int32] // flat N×N: code(x)·N + code(y) → code(x+y)
}

///|
fn elem_code(p : Int32, nvars : Int32, x : Array[Int32]) -> Int32 {
  // little-endian mixed-radix code == index inside `all_elements()`
  // (enumerate_vectors pushes x % p first, so coord 0 is the lowest digit)
  let mut c = 0
  let mut place = 1
  for k in 0..<nvars {
    c = c + x[k] * place
    place = place * p
  }
  c
}

///|
/// Localize at a multiplicatively closed subset `S` (1 is auto-added if
/// missing; non-closed `S` aborts). Cost: O(|R|²·|S|) once.
pub fn FinAlg::localize(
  self : Self,
  s_members : Array[Array[Int32]],
) -> Localization {
  let p = self.p
  let nvars = self.dim
  let mut s_set = @linalg.elems_normalize(p, s_members)
  if !@linalg.elems_contains(s_set, self.one_elem()) {
    let with_one : Array[Array[Int32]] = [self.one_elem()]
    for x in s_set {
      with_one.push(x)
    }
    s_set = @linalg.elems_normalize(p, with_one)
  }
  let elems = self.all_elements()
  let n = elems.length()
  let s_codes : Array[Int32] = []
  let s_idx_of : Array[Int32] = []
  for _c in 0..<n {
    s_idx_of.push(-1)
  }
  for si in 0..<s_set.length() {
    let code = elem_code(p, nvars, s_set[si])
    s_codes.push(code)
    s_idx_of[code] = si
  }
  // arithmetic tables over codes
  let mul_code : Array[Int32] = []
  let add_code : Array[Int32] = []
  for _i in 0..<(n * n) {
    mul_code.push(0)
    add_code.push(0)
  }
  for x in 0..<n {
    for y in 0..<n {
      let prod = self.mul_elem(elems[x], elems[y])
      let sum = @linalg.vec_add(p, elems[x], elems[y])
      mul_code[x * n + y] = elem_code(p, nvars, prod)
      add_code[x * n + y] = elem_code(p, nvars, sum)
    }
  }
  // closure of S under multiplication (codes)
  for a in s_codes {
    for b in s_codes {
      if s_idx_of[mul_code[a * n + b]] == -1 {
        abort("FinAlg::localize: S is not multiplicatively closed")
      }
    }
  }
  // pairs (a, s)
  let npairs = n * s_set.length()
  let pair_num : Array[Int32] = []
  let pair_den : Array[Int32] = []
  for a in 0..<n {
    for si in 0..<s_set.length() {
      pair_num.push(a)
      pair_den.push(si)
    }
  }
  // build classing incrementally: class_of assigned during a mutable pass
  // equivalence over raw arrays (no struct needed)
  fn equiv_raw(
    s_codes : Array[Int32],
    pair_num : Array[Int32],
    pair_den : Array[Int32],
    mul_code : Array[Int32],
    elems : Array[Array[Int32]],
    p : Int32,
    nvars : Int32,
    n : Int32,
    i : Int32,
    j : Int32,
  ) -> Bool {
    let den_i = s_codes[pair_den[i]]
    let den_j = s_codes[pair_den[j]]
    let at = mul_code[pair_num[i] * n + den_j]
    let bs = mul_code[pair_num[j] * n + den_i]
    let w = @linalg.vec_add(p, elems[at], @linalg.vec_scale(p, -1, elems[bs]))
    let wc = elem_code(p, nvars, w)
    for c in s_codes {
      if mul_code[c * n + wc] == 0 {
        return true
      }
    }
    false
  }
  let pc : Array[Int32] = []
  for _i in 0..<npairs {
    pc.push(-1)
  }
  let cp : Array[Int32] = []
  let mut cc = 0
  for id in 0..<npairs {
    if pc[id] != -1 {
      continue
    }
    pc[id] = cc
    cp.push(id)
    cc = cc + 1
    for j in (id + 1)..<npairs {
      if pc[j] == -1 {
        if equiv_raw(
            s_codes, pair_num, pair_den, mul_code, elems, p, nvars, n, id, j,
          ) {
          pc[j] = pc[id]
        }
      }
    }
  }
  Localization::{
    base: self,
    s_set,
    s_codes,
    s_idx_of,
    pair_num,
    pair_den,
    pair_class: pc,
    class_count: cc,
    class_pair: cp,
    mul_code,
    add_code,
  }
}

///|
/// Localize at the complement of a maximal ideal: `S = R ∖ m` (gives `R_m`).
pub fn FinAlg::localize_at(self : Self, m : FinIdeal) -> Localization {
  let s : Array[Array[Int32]] = []
  for x in self.all_elements() {
    if !m.contains(x) {
      s.push(x)
    }
  }
  self.localize(s)
}

///|
/// Localization at powers of an element: `S = {1, f, f², …}` (finite set —
/// stabilize when a power repeats).
pub fn FinAlg::localize_at_element(
  self : Self,
  f : Array[Int32],
) -> Localization {
  // build S = {f^k} starting from 1 (0 only enters if f nilpotent → S grows to whole ring)
  let mut acc = self.one_elem()
  let out : Array[Array[Int32]] = []
  let mut k = 0
  // distinct powers of f number at most |R| — repeat is forced after that
  let bound = @num.power_int(self.p, self.dim) + 1
  while k <= bound {
    if !@linalg.elems_contains(out, acc) {
      out.push(acc)
    }
    acc = self.mul_elem(acc, f)
    k = k + 1
  }
  self.localize(out)
}

///|
/// Number of elements of `R_S`.
pub fn Localization::size(self : Self) -> Int32 {
  self.class_count
}

///|
/// Class of the fraction `a/s` (requires `s ∈ S`).
pub fn Localization::fraction(
  self : Self,
  a : Array[Int32],
  s : Array[Int32],
) -> Int32 {
  let si = self.s_idx_of[elem_code(self.base.p, self.base.dim, s)]
  if si == -1 {
    abort("Localization::fraction: denominator not in S")
  }
  let aid = elem_code(self.base.p, self.base.dim, a) * self.s_codes.length() +
    si
  self.pair_class[aid]
}

///|
/// The image of `x ∈ R` under `R → R_S`.
pub fn Localization::embed(self : Self, x : Array[Int32]) -> Int32 {
  self.fraction(x, self.base.one_elem())
}

///|
/// Product of two classes.
pub fn Localization::mul_class(self : Self, c1 : Int32, c2 : Int32) -> Int32 {
  let ne = self.base.all_elements().length()
  let i1 = self.class_pair[c1]
  let i2 = self.class_pair[c2]
  let num = self.mul_code[self.pair_num[i1] * ne + self.pair_num[i2]]
  let d1 = self.s_codes[self.pair_den[i1]]
  let d2 = self.s_codes[self.pair_den[i2]]
  let den_code = self.mul_code[d1 * ne + d2]
  let si = self.s_idx_of[den_code]
  if si == -1 {
    abort("Localization::mul_class: denominator left S (closure violated)")
  }
  self.pair_class[num * self.s_codes.length() + si]
}

///|
/// Sum of two classes `(a/s) + (b/t) = (a·t + b·s)/(s·t)`.
pub fn Localization::add_class(self : Self, c1 : Int32, c2 : Int32) -> Int32 {
  let ne = self.base.all_elements().length()
  let i1 = self.class_pair[c1]
  let i2 = self.class_pair[c2]
  let d1 = self.s_codes[self.pair_den[i1]]
  let d2 = self.s_codes[self.pair_den[i2]]
  let at = self.mul_code[self.pair_num[i1] * ne + d2]
  let bs = self.mul_code[self.pair_num[i2] * ne + d1]
  let num = self.add_code[at * ne + bs]
  let den_code = self.mul_code[d1 * ne + d2]
  let si = self.s_idx_of[den_code]
  if si == -1 {
    abort("Localization::add_class: denominator left S (closure violated)")
  }
  self.pair_class[num * self.s_codes.length() + si]
}

///|
/// The canonical map `R_S → R_T` induced by `S ⊆ T` (same base ring):
/// every class maps via a representative pair. Theorem: this map is a
/// well-defined surjective ring homomorphism whenever `S ⊆ T`.
pub fn Localization::map_to(self : Self, other : Localization) -> Array[Int32] {
  if self.base.p != other.base.p || self.base.dim != other.base.dim {
    abort("Localization::map_to: different base rings")
  }
  for s in self.s_set {
    if other.s_idx_of[elem_code(other.base.p, other.base.dim, s)] == -1 {
      abort("Localization::map_to: S ⊄ T")
    }
  }
  let table : Array[Int32] = []
  for _c in 0..<self.class_count {
    table.push(-1)
  }
  for c in 0..<self.class_count {
    let rep = self.class_pair[c]
    let a = self.pair_num[rep]
    let s = self.s_codes[self.pair_den[rep]]
    let si = other.s_idx_of[s]
    let aid = a * other.s_codes.length() + si
    table[c] = other.pair_class[aid]
  }
  table
}
