///|
/// A term `c · x^e` of a multivariate polynomial, with `c ∈ ℤ/mℤ` and
/// exponent vector `e = (e_0, ..., e_{n-1})`.
pub(all) struct Term {
  coeff : IntMod
  exp : Array[Int32]
} derive(Debug, Eq)

///|
/// Lexicographic order on exponent vectors with `x_0 > x_1 > ... > x_{n-1}`:
/// the first differing coordinate decides (larger exponent wins).
/// This is a admissible (well-ordering) monomial order, hence Gröbner theory
/// applies; making `x_0` dominant enables variable elimination.
pub fn lex_cmp(a : Array[Int32], b : Array[Int32]) -> Int32 {
  if a.length() != b.length() {
    abort("lex_cmp: dimension mismatch")
  }
  for i in 0..<a.length() {
    if a[i] != b[i] {
      return a[i].compare(b[i])
    }
  }
  0
}

///|
/// Does monomial `a` divide monomial `b` (componentwise `a <= b`)?
pub fn exp_divides(a : Array[Int32], b : Array[Int32]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if a[i] > b[i] {
      return false
    }
  }
  true
}

///|
/// Componentwise lcm of two exponent vectors.
pub fn exp_lcm(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<a.length() {
    out.push(if a[i] > b[i] { a[i] } else { b[i] })
  }
  out
}

///|
/// Componentwise sum `a + b` (the exponent of a product of monomials).
pub fn exp_add(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<a.length() {
    out.push(a[i] + b[i])
  }
  out
}

///|
/// Definition (polynomial ring `k[x_0, ..., x_{n-1}]`): finite `k`-linear
/// combinations of monomials `x^e`. Internally: terms sorted by *descending*
/// lex order with unique exponents and nonzero coefficients — the canonical
/// form, so structural equality coincides with polynomial equality.
pub(all) struct Poly {
  nvars : Int32
  modulus : Int32
  terms : Array[Term]
} derive(Debug, Eq)

///|
/// Build a polynomial from raw `(coefficient, exponent)` pairs; normalizes
/// (reduces coefficients mod `m`, merges like terms, drops zeros, sorts lex
/// descending). This is the single canonicalization point of the module.
pub fn poly_of_terms(
  nvars : Int32,
  modulus : Int32,
  raw : Array[(Int32, Array[Int32])],
) -> Poly {
  if modulus < 2 {
    abort("poly: modulus must be >= 2")
  }
  for (_, e) in raw {
    if e.length() != nvars {
      abort("poly: exponent dimension mismatch")
    }
  }
  // accumulate coefficients per exponent (linear scan; sizes stay small)
  let exps : Array[Array[Int32]] = []
  let coeffs : Array[Int32] = []
  for (c, e) in raw {
    let cc = @num.mod_pos(c, modulus)
    let mut found = -1
    for i in 0..<exps.length() {
      if lex_cmp(exps[i], e) == 0 {
        found = i
      }
    }
    if found == -1 {
      exps.push(e)
      coeffs.push(cc)
    } else {
      coeffs[found] = @num.mod_pos(coeffs[found] + cc, modulus)
    }
  }
  let terms : Array[Term] = []
  for i in 0..<exps.length() {
    if coeffs[i] != 0 {
      terms.push(Term::{
        coeff: IntMod::make(modulus, coeffs[i]),
        exp: exps[i],
      })
    }
  }
  terms.sort_by(fn(a, b) { lex_cmp(b.exp, a.exp) }) // descending
  Poly::{ nvars, modulus, terms, }
}

///|
/// The zero polynomial with ambient data (`nvars`, `modulus`).
pub fn Poly::zero(nvars : Int32, modulus : Int32) -> Poly {
  Poly::{ nvars, modulus, terms: [], }
}

///|
/// The zero exponent vector of length `nvars`.
fn zero_exp(nvars : Int32) -> Array[Int32] {
  let e : Array[Int32] = []
  for _k in 0..<nvars {
    e.push(0)
  }
  e
}

///|
/// The unit polynomial `1`.
pub fn Poly::one(nvars : Int32, modulus : Int32) -> Poly {
  poly_of_terms(nvars, modulus, [(1, zero_exp(nvars))])
}

///|
/// A constant polynomial `c`.
pub fn Poly::constant(nvars : Int32, modulus : Int32, c : Int32) -> Poly {
  poly_of_terms(nvars, modulus, [(c, zero_exp(nvars))])
}

///|
/// The variable polynomial `x_i`.
pub fn Poly::variable(nvars : Int32, modulus : Int32, i : Int32) -> Poly {
  if i < 0 || i >= nvars {
    abort("Poly::var: index out of range")
  }
  let e : Array[Int32] = []
  for k in 0..<nvars {
    e.push(if k == i { 1 } else { 0 })
  }
  poly_of_terms(nvars, modulus, [(1, e)])
}

///|
/// Is this the zero polynomial?
pub fn Poly::is_zero(self : Self) -> Bool {
  self.terms.length() == 0
}

///|
/// Leading monomial exponent (lex-max), `None` for the zero polynomial.
pub fn Poly::lm(self : Self) -> Array[Int32]? {
  if self.terms.length() == 0 {
    None
  } else {
    Some(self.terms[0].exp)
  }
}

///|
/// Leading coefficient, zero for the zero polynomial.
pub fn Poly::lc(self : Self) -> IntMod {
  if self.terms.length() == 0 {
    IntMod::make(self.modulus, 0)
  } else {
    self.terms[0].coeff
  }
}

///|
/// Total degree of the leading monomial (`-1` for zero).
pub fn Poly::total_deg(self : Self) -> Int32 {
  if self.terms.length() == 0 {
    return -1
  }
  let mut d = 0
  for x in self.terms[0].exp {
    d = d + x
  }
  d
}

///|
/// Polynomial addition (componentwise on canonical forms).
// 將 Ring 方法顯式掛回 Poly（避免 implicit promotion 廢棄警告）
extend Poly with Ring::{add, sub, mul, zero_like}

///|
pub impl Ring for Poly with fn add(self, other) {
  if self.nvars != other.nvars || self.modulus != other.modulus {
    abort("Poly::add: ambient mismatch")
  }
  let raw : Array[(Int32, Array[Int32])] = []
  for t in self.terms {
    raw.push((t.coeff.val, t.exp))
  }
  for t in other.terms {
    raw.push((t.coeff.val, t.exp))
  }
  poly_of_terms(self.nvars, self.modulus, raw)
}

///|
pub impl Ring for Poly with fn sub(self, other) {
  if self.nvars != other.nvars || self.modulus != other.modulus {
    abort("Poly::sub: ambient mismatch")
  }
  let raw : Array[(Int32, Array[Int32])] = []
  for t in self.terms {
    raw.push((t.coeff.val, t.exp))
  }
  for t in other.terms {
    raw.push((-t.coeff.val, t.exp))
  }
  poly_of_terms(self.nvars, self.modulus, raw)
}

///|
/// Polynomial multiplication: every pair of terms multiplied, then canonicalized.
pub impl Ring for Poly with fn mul(self, other) {
  if self.nvars != other.nvars || self.modulus != other.modulus {
    abort("Poly::mul: ambient mismatch")
  }
  let raw : Array[(Int32, Array[Int32])] = []
  for a in self.terms {
    for b in other.terms {
      raw.push(
        (
          @num.mul_mod(a.coeff.val, b.coeff.val, self.modulus),
          exp_add(a.exp, b.exp),
        ),
      )
    }
  }
  poly_of_terms(self.nvars, self.modulus, raw)
}

///|
pub impl Ring for Poly with fn neg(self) {
  let raw : Array[(Int32, Array[Int32])] = []
  for t in self.terms {
    raw.push((-t.coeff.val, t.exp))
  }
  poly_of_terms(self.nvars, self.modulus, raw)
}

///|
pub impl Ring for Poly with fn zero_like(self) {
  Poly::zero(self.nvars, self.modulus)
}

///|
pub impl Ring for Poly with fn one_like(self) {
  Poly::one(self.nvars, self.modulus)
}

///|
/// Multiply by a single monomial `c · x^e`.
pub fn Poly::mul_monom(self : Self, c : Int32, e : Array[Int32]) -> Poly {
  let raw : Array[(Int32, Array[Int32])] = []
  for t in self.terms {
    raw.push((t.coeff.val * c, exp_add(t.exp, e)))
  }
  poly_of_terms(self.nvars, self.modulus, raw)
}

///|
/// Drop the leading term (used by the division algorithm).
fn pop_lead(p : Poly) -> Poly {
  if p.terms.length() == 0 {
    return p
  }
  let raw : Array[(Int32, Array[Int32])] = []
  for i in 1..<p.terms.length() {
    raw.push((p.terms[i].coeff.val, p.terms[i].exp))
  }
  poly_of_terms(p.nvars, p.modulus, raw)
}

///|
/// Multivariate division with remainder: given `g_1, ..., g_s`, compute
/// quotients `q_i` and remainder `r` with `f = Σ q_i g_i + r` such that no
/// monomial of `r` is divisible by any `lm(g_i)` (when coefficients invert;
/// over a field this is the classical exact algorithm).
/// Complexity: `O(s · terms(f) · terms(g))` worst case.
pub fn Poly::divmod(self : Self, gs : Array[Poly]) -> (Array[Poly], Poly) {
  let qs : Array[Poly] = []
  for _i in 0..<gs.length() {
    qs.push(Poly::zero(self.nvars, self.modulus))
  }
  let mut r = self
  let rem_terms : Array[(Int32, Array[Int32])] = []
  let mut steps = 0
  while !r.is_zero() {
    steps = steps + 1
    if steps > 200000 {
      abort("divmod: iteration limit exceeded")
    }
    let rlm = match r.lm() {
      Some(e) => e
      None => break
    }
    let mut reduced = false
    for i in 0..<gs.length() {
      let g = gs[i]
      if g.is_zero() {
        continue
      }
      let glm = match g.lm() {
        Some(e) => e
        None => continue
      }
      if !exp_divides(glm, rlm) {
        continue
      }
      match g.lc().try_inv() {
        Some(ginv) => {
          let c = r.lc().mul(ginv)
          let e : Array[Int32] = []
          for k in 0..<self.nvars {
            e.push(rlm[k] - glm[k])
          }
          let qterm = poly_of_terms(self.nvars, self.modulus, [(c.val, e)])
          qs[i] = qs[i].add(qterm)
          r = r.sub(qterm.mul(g))
          reduced = true
          break
        }
        None =>
          // coefficient not invertible (composite modulus): treat as
          // non-divisible — this yields a weak normal form.
          ()
      }
    }
    if !reduced {
      rem_terms.push((r.lc().val, rlm))
      r = pop_lead(r)
    }
  }
  let rem = poly_of_terms(self.nvars, self.modulus, rem_terms)
  (qs, rem)
}

///|
/// Remainder of `f` on division by `gs` (the normal form).
pub fn Poly::normal_form(self : Self, gs : Array[Poly]) -> Poly {
  let (_, r) = self.divmod(gs)
  r
}

///|
/// Evaluate at a point `p ∈ (ℤ/mℤ)^n` (used by affine varieties).
pub fn Poly::eval(self : Self, pt : Array[Int32]) -> IntMod {
  if pt.length() != self.nvars {
    abort("Poly::eval: point dimension mismatch")
  }
  let mut acc = IntMod::make(self.modulus, 0)
  for t in self.terms {
    let mut m = t.coeff
    for k in 0..<self.nvars {
      if t.exp[k] > 0 {
        for _i in 0..<t.exp[k] {
          m = m.mul(IntMod::make(self.modulus, pt[k]))
        }
      }
    }
    acc = acc.add(m)
  }
  acc
}

///|
/// 形式導數（定義）：`∂/∂x_k (c·x^e) = c·e_k·x^(e−ε_k)`，係數在 `ℤ/mℤ` 內
/// 乘法（特徵 `p | e_k` 時該項消失 — Frobenius：`∂(x^p) = 0`）。
///
/// 性質（見根包性質測試）：`∂` 是 `𝔽_p`-線性的，且滿足萊布尼茲法則
/// `∂(f·g) = ∂f·g + f·∂g`；`∂` 與平移交換：`∂_k(f(x+a)) = (∂_k f)(x+a)`。
pub fn Poly::derivative(self : Self, k : Int32) -> Poly {
  if k < 0 || k >= self.nvars {
    abort("Poly::derivative: variable index out of range")
  }
  let raw : Array[(Int32, Array[Int32])] = []
  for t in self.terms {
    let ek = t.exp[k]
    if ek > 0 {
      let c = IntMod::make(t.coeff.modulus, t.coeff.rep() * ek)
      if c.rep() != 0 {
        let e2 : Array[Int32] = []
        for j in 0..<self.nvars {
          e2.push(if j == k { ek - 1 } else { t.exp[j] })
        }
        raw.push((c.rep(), e2))
      }
    }
  }
  poly_of_terms(self.nvars, self.modulus, raw)
}
