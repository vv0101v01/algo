///|
/// Nilpotent power bound for finite algebras: if `x^n = 0` then
/// `x^k = 0` for some `k ≤ dim R`.
/// Proof: the powers `1, x, x², …, x^d` (d = dim R) are linearly
/// dependent, giving `c·x^d + … + c₀ = 0`; if `c₀ ≠ 0` then `x` is a unit,
/// contradiction — so `x^j·(c_d x^{d−j} + … + c₀) = 0` with `x^j` minimal
/// nilpotent index, `j < d`. In a commutative ring the minimal index k
/// satisfies `k ≤ d`. (We simply scan up to `d + 1` steps for safety.)
fn nilpotent_index(alg : FinAlg, x : Array[Int32]) -> Int32 {
  let mut cur = x
  let mut k = 1
  let bound = alg.dim + 1
  while k <= bound {
    let mut is_zero = true
    for v in cur {
      if v != 0 {
        is_zero = false
      }
    }
    if is_zero {
      return k
    }
    cur = alg.mul_elem(cur, x)
    k = k + 1
  }
  -1 // not nilpotent
}

///|
/// Is `x` nilpotent (∃k>0: xᵏ = 0)? Exact for finite rings by bound above.
pub fn is_nilpotent(alg : FinAlg, x : Array[Int32]) -> Bool {
  nilpotent_index(alg, x) != -1
}

///|
/// The nilradical `√⟨0⟩`: all nilpotent elements (an ideal; in a commutative
/// ring it equals the Jacobson radical — verified as a property test).
pub fn nilradical(alg : FinAlg) -> FinIdeal {
  let out : Array[Array[Int32]] = []
  for a in alg.all_elements() {
    if is_nilpotent(alg, a) {
      out.push(a)
    }
  }
  FinIdeal::{ alg, members: @linalg.elems_normalize(alg.p, out), }
}

///|
/// Is the ring reduced (no nonzero nilpotents)?
pub fn is_reduced(alg : FinAlg) -> Bool {
  for a in alg.all_elements() {
    let mut z = true
    for v in a {
      if v != 0 {
        z = false
      }
    }
    if z {
      continue
    }
    if is_nilpotent(alg, a) {
      return false
    }
  }
  true
}

///|
/// Jacobson radical `J(R) = ∩ {maximal ideals}` computed by explicit
/// intersection. Theorem (commutative, any ring): `J(R) = √⟨0⟩ = Nil(R)`.
pub fn jacobson_radical(alg : FinAlg) -> FinIdeal {
  let ms = maximal_ideals(alg)
  if ms.length() == 0 {
    return alg.unit_ideal() // degenerate: no maximals (zero ring) — vacuous ∩
  }
  let mut acc = ms[0]
  for k in 1..<ms.length() {
    acc = acc.intersect(ms[k])
  }
  acc
}

///|
/// Radical of an ideal: `√I = { x : xᵏ ∈ I for some k }`.
/// Theorem (finite rings): the bound `k ≤ dim(R/I)` is exact — if `x ∉ I`
/// is nilpotent mod `I`, its index in `R/I` is at most `dim(R/I)`.
pub fn FinIdeal::radical(self : Self) -> FinIdeal {
  let p = self.alg.p
  let dim_q = self.alg.dim - ideal_dim(self) // dim R − dim_k I
  let bound = if dim_q > 0 { dim_q } else { 1 }
  let out : Array[Array[Int32]] = []
  for x in self.alg.all_elements() {
    if self.contains(x) {
      out.push(x)
      continue
    }
    let mut cur = x
    let mut k = 1
    let mut hit = false
    while k <= bound {
      if self.contains(cur) {
        hit = true
      }
      cur = self.alg.mul_elem(cur, x)
      k = k + 1
    }
    if hit {
      out.push(x)
    }
  }
  FinIdeal::{ alg: self.alg, members: @linalg.elems_normalize(p, out), }
}

///|
/// Is `I` semiprime (radical: contains no nonzero nilpotents modulo itself)?
/// Equivalent finite test: `I = √I` via the radical bound above.
pub fn FinIdeal::is_semiprime(self : Self) -> Bool {
  self.eq(self.radical())
}

///|
/// All idempotents `e² = e` of the algebra (an `𝔽_p`-subspace for
/// commutative rings — the product of orthogonal idempotents sums).
pub fn idempotents(alg : FinAlg) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for a in alg.all_elements() {
    if @linalg.vec_eq(alg.mul_elem(a, a), a) {
      out.push(a)
    }
  }
  out
}

///|
fn is_zero_vec(v : Array[Int32]) -> Bool {
  for x in v {
    if x != 0 {
      return false
    }
  }
  true
}

///|
fn is_one_vec(alg : FinAlg, v : Array[Int32]) -> Bool {
  @linalg.vec_eq(v, alg.one_elem())
}

///|
/// The trivial idempotents `0` and `1`.
pub fn is_trivial_idempotent(alg : FinAlg, e : Array[Int32]) -> Bool {
  if !@linalg.vec_eq(alg.mul_elem(e, e), e) {
    return false
  }
  is_zero_vec(e) || is_one_vec(alg, e)
}

///|
/// Is `e` a primitive idempotent (indecomposable)? Definition (as used in
/// this library, tuned for block decompositions): `e` is a NONTRIVIAL
/// idempotent `0 < e < 1` with **no** orthogonal decomposition `e = a + b`,
/// `ab = 0`, `a, b ≠ 0` idempotents. The trivial idempotents `0, 1` are
/// not counted as primitive (they correspond to the empty/whole block).
pub fn is_primitive_idempotent(alg : FinAlg, e : Array[Int32]) -> Bool {
  if !@linalg.vec_eq(alg.mul_elem(e, e), e) {
    return false
  }
  if is_zero_vec(e) || is_one_vec(alg, e) {
    return false
  }
  // search for a nontrivial orthogonal split
  for a in idempotents(alg) {
    if is_zero_vec(a) {
      continue
    }
    if @linalg.vec_eq(a, e) {
      continue
    }
    // b = e − a
    let b = @linalg.vec_add(alg.p, e, @linalg.vec_scale(alg.p, -1, a))
    if is_zero_vec(b) {
      continue
    }
    if @linalg.vec_eq(alg.mul_elem(b, b), b) && is_zero_vec(alg.mul_elem(a, b)) {
      return false // found a split e = a + b
    }
  }
  true
}

///|
/// All primitive idempotents of the algebra.
pub fn primitive_idempotents(alg : FinAlg) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for e in idempotents(alg) {
    if is_primitive_idempotent(alg, e) {
      out.push(e)
    }
  }
  out
}

///|
/// A nontrivial split of `e` as `(a, b)` with `e = a + b`, `ab = 0`, both
/// nonzero idempotents, or `None` if `e` is primitive/indecomposable.
pub fn split_idempotent(
  alg : FinAlg,
  e : Array[Int32],
) -> (Array[Int32], Array[Int32])? {
  for a in idempotents(alg) {
    if is_zero_vec(a) || @linalg.vec_eq(a, e) {
      continue
    }
    let b = @linalg.vec_add(alg.p, e, @linalg.vec_scale(alg.p, -1, a))
    if is_zero_vec(b) {
      continue
    }
    if @linalg.vec_eq(alg.mul_elem(b, b), b) && is_zero_vec(alg.mul_elem(a, b)) {
      return Some((a, b))
    }
  }
  None
}

///|
/// The corner subalgebra `e·R = {x ∈ eR}` as a `FinAlg` — the unit is `e`
/// itself (forced to basis index 0 by `subalgebra`).
pub fn corner(alg : FinAlg, e : Array[Int32]) -> FinAlg {
  let elems : Array[Array[Int32]] = []
  for x in alg.all_elements() {
    elems.push(alg.mul_elem(e, x))
  }
  FinAlg::subalgebra(alg, elems, e)
}

///|
/// Krull–Schmidt block decomposition `R ≅ ∏ R_i` into rings with no
/// nontrivial idempotents (indecomposable factors), by recursively cutting
/// along any nontrivial idempotent.
/// Theorem: the number of blocks and the multiset of block isomorphism
/// classes are unique (Krull–Schmidt).
pub fn decompose_blocks(alg : FinAlg) -> Array[FinAlg] {
  fn no_split(alg : FinAlg) -> Bool {
    for e in idempotents(alg) {
      if !is_trivial_idempotent(alg, e) {
        return false
      }
    }
    true
  }
  fn rec(alg : FinAlg, acc : Array[FinAlg]) -> Unit {
    if no_split(alg) {
      acc.push(alg)
      return
    }
    let mut split_e : Array[Int32] = []
    for e in idempotents(alg) {
      if !is_trivial_idempotent(alg, e) {
        split_e = e
      }
    }
    let a = corner(alg, split_e)
    let comp = @linalg.vec_add(
      alg.p,
      alg.one_elem(),
      @linalg.vec_scale(alg.p, -1, split_e),
    )
    let b = corner(alg, comp)
    rec(a, acc)
    rec(b, acc)
  }
  let acc : Array[FinAlg] = []
  rec(alg, acc)
  acc
}
