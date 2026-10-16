///|
/// A finite commutative unital algebra over a prime field `𝔽_p`, given by
/// structure constants: `mult[i]` is the matrix of multiplication-by-`e_i`
/// on the `𝔽_p`-basis `(e_0 = 1, e_1, ..., e_{d-1})`, i.e.
/// `mult[i][w][j] = coord_w(e_i · e_j)`.
///
/// Every finite ring that appears as a coordinate ring, quotient, or product
/// in this library is represented this way; all ring-theoretic questions
/// (ideals, primes, radicals, idempotents, conductors, localizations) then
/// reduce to exact linear algebra over `𝔽_p` plus finite scans.
pub(all) struct FinAlg {
  p : Int32
  dim : Int32
  mult : Array[@linalg.Matrix] // length = dim; each dim × dim
} derive(Debug)

///|
/// All `p^dim` elements as coordinate vectors (ascending mixed-radix order),
/// capped for safety.
pub fn FinAlg::all_elements(self : Self) -> Array[Array[Int32]] {
  @linalg.enumerate_vectors(self.p, self.dim)
}

///|
/// The zero element `0 = (0, ..., 0)`.
pub fn FinAlg::zero_elem(self : Self) -> Array[Int32] {
  let e : Array[Int32] = []
  for _i in 0..<self.dim {
    e.push(0)
  }
  e
}

///|
/// The unit element `1 = e_0` (basis index 0 must be the identity).
pub fn FinAlg::one_elem(self : Self) -> Array[Int32] {
  let e : Array[Int32] = []
  for i in 0..<self.dim {
    e.push(if i == 0 { 1 } else { 0 })
  }
  e
}

///|
/// Componentwise sum in `𝔽_p^d`.
pub fn FinAlg::add_elem(
  self : Self,
  a : Array[Int32],
  b : Array[Int32],
) -> Array[Int32] {
  @linalg.vec_add(self.p, a, b)
}

///|
/// Negation.
pub fn FinAlg::neg_elem(self : Self, a : Array[Int32]) -> Array[Int32] {
  @linalg.vec_scale(self.p, -1, a)
}

///|
/// Product `Σ_i a_i · (mult[i] · b)` — the structure-constant multiplication.
pub fn FinAlg::mul_elem(
  self : Self,
  a : Array[Int32],
  b : Array[Int32],
) -> Array[Int32] {
  if a.length() != self.dim || b.length() != self.dim {
    abort("mul_elem: dimension mismatch")
  }
  let p = self.p
  let out : Array[Int32] = []
  for _w in 0..<self.dim {
    out.push(0)
  }
  for i in 0..<self.dim {
    let ai = a[i]
    if ai != 0 {
      let mb = self.mult[i].apply(b)
      for w in 0..<self.dim {
        out[w] = @num.mod_pos(out[w] + @num.mul_mod(ai, mb[w], p), p)
      }
    }
  }
  out
}

///|
/// Structural check: `e_0` is a two-sided unit and multiplication is
/// commutative (checked on basis products, which suffices by bilinearity).
pub fn FinAlg::validate(self : Self) -> Bool {
  if self.mult.length() != self.dim {
    return false
  }
  let one = self.one_elem()
  for j in 0..<self.dim {
    let ej : Array[Int32] = []
    for k in 0..<self.dim {
      ej.push(if k == j { 1 } else { 0 })
    }
    if !@linalg.int_arrays_eq(self.mul_elem(one, ej), ej) {
      return false
    }
    for i in 0..<self.dim {
      let ei : Array[Int32] = []
      for k in 0..<self.dim {
        ei.push(if k == i { 1 } else { 0 })
      }
      let ij = self.mul_elem(ei, ej)
      let ji = self.mul_elem(ej, ei)
      if !@linalg.int_arrays_eq(ij, ji) {
        return false
      }
    }
  }
  true
}

///|
/// The algebra `𝔽_p[x]/⟨f⟩` with `f` monic of degree `d ≥ 1`
/// (input: ascending coefficients `[c_0, ..., c_d]`, `c_d ≠ 0 mod p`).
/// Basis: `(1, x, ..., x^{d-1})`; multiplication by `x` is the companion
/// matrix of `f`. Theorem: `dim = deg f`, and the ring is a field iff `f`
/// is irreducible.
pub fn FinAlg::univariate_quotient(p : Int32, coeffs : Array[Int32]) -> FinAlg {
  let d = coeffs.length() - 1
  if d < 1 {
    abort("univariate_quotient: degree must be >= 1")
  }
  let lc = @num.mod_pos(coeffs[d], p)
  let linv = match @num.invmod(lc, p) {
    Some(x) => x
    None => abort("univariate_quotient: leading coefficient must be a unit")
  }
  // monic coefficients
  let mono : Array[Int32] = []
  for c in coeffs {
    mono.push(@num.mul_mod(c, linv, p))
  }
  // M_x: columns 0..d-2 are e_{j+1}; last column = -(c_0, ..., c_{d-1})
  let mx = @linalg.Matrix::zero(p, d, d)
  for j in 0..<(d - 1) {
    mx.data[j + 1][j] = 1
  }
  for i in 0..<d {
    mx.data[i][d - 1] = @num.mod_pos(-mono[i], p)
  }
  let mult : Array[@linalg.Matrix] = []
  // mult[0] = I (multiplication by 1)
  mult.push(@linalg.Matrix::identity(p, d))
  let mut acc = mx
  for _i in 1..<d {
    mult.push(acc.copy())
    acc = acc.mul(mx)
  }
  FinAlg::{ p, dim: d, mult, }
}

///|
/// The algebra `𝔽_p[x_0..x_{n-1}] / I` for a zero-dimensional ideal `I`
/// (aborts if the quotient is infinite): basis = standard monomials with
/// `1` forced to index `0`; `mult[i]` built from `m_i · m_j` reduced by the
/// Gröbner basis of `I`.
/// Theorem: `dim = Π_k a_k` (pure-power bounds of `I`).
pub fn FinAlg::zero_dim_quotient(p : Int32, gens : Array[@poly.Poly]) -> FinAlg {
  let basis = match @poly.standard_monomials(gens) {
    Some(b) => b
    None => abort("zero_dim_quotient: quotient is infinite-dimensional")
  }
  let d = basis.length()
  if d > 64 {
    // standard_monomials already bounds the total by p^d ≤ 100000;
    // the structure-matrix build costs O(d² · GB) which stays cheap.
    abort("zero_dim_quotient: dim > 64 not supported")
  }
  // move the monomial 1 = (0,...,0) to index 0
  let b : Array[Array[Int32]] = []
  for x in basis {
    b.push(x)
  }
  let mut i0 = -1
  for i in 0..<d {
    let mut allz = true
    for k in 0..<b[i].length() {
      if b[i][k] != 0 {
        allz = false
      }
    }
    if allz {
      i0 = i
    }
  }
  if i0 > 0 {
    let t = b[0]
    b[0] = b[i0]
    b[i0] = t
  }
  let gb = @poly.groebner_basis(gens)
  let mult : Array[@linalg.Matrix] = []
  for i in 0..<d {
    let mi = @linalg.Matrix::zero(p, d, d)
    for j in 0..<d {
      let e : Array[Int32] = []
      for k in 0..<b[i].length() {
        e.push(b[i][k] + b[j][k])
      }
      let prod = @poly.poly_of_terms(b[i].length(), p, [(1, e)])
      let red = prod.normal_form(gb)
      for t in red.terms {
        let mut idx = -1
        for r in 0..<d {
          if @linalg.int_arrays_eq(b[r], t.exp) {
            idx = r
          }
        }
        if idx == -1 {
          abort("zero_dim_quotient: reduction left the standard monomial span")
        }
        mi.data[idx][j] = t.coeff.val
      }
    }
    mult.push(mi)
  }
  let alg = FinAlg::{ p, dim: d, mult, }
  if !alg.validate() {
    abort("zero_dim_quotient: produced structure failed validation")
  }
  alg
}

///|
/// The direct product `𝔽_p^{d_1} × ... × 𝔽_p^{d_k}` with componentwise
/// arithmetic; basis vectors are the orthogonal idempotent units.
/// Theorem (CRT): such products classify semisimple finite algebras.
pub fn FinAlg::product(p : Int32, dims : Array[Int32]) -> FinAlg {
  let mut total = 0
  for d in dims {
    if d < 1 {
      abort("FinAlg::product: factors must have dim >= 1")
    }
    total = total + d
  }
  if total == 0 {
    abort("FinAlg::product: at least one factor required")
  }
  // Basis: e_0 = 1 = u_1 + … + u_k (the ring identity MUST sit at index 0),
  // e_i = u_{i+1} (i ≥ 1): the remaining orthogonal idempotents.
  // Mult-by-e_0 = identity; mult-by-e_i (i ≥ 1): e_i·1 = e_i and e_i·e_i = e_i.
  let mult : Array[@linalg.Matrix] = []
  for i in 0..<total {
    let mi = @linalg.Matrix::zero(p, total, total)
    if i == 0 {
      for j in 0..<total {
        mi.data[j][j] = 1
      }
    } else {
      mi.data[i][0] = 1
      mi.data[i][i] = 1
    }
    mult.push(mi)
  }
  let alg = FinAlg::{ p, dim: total, mult, }
  if !alg.validate() {
    abort("FinAlg::product: produced structure failed validation")
  }
  alg
}

///|
/// Subalgebra generated by a closed subset: `elems` must be an
/// `𝔽_p`-subspace of the ambient algebra closed under multiplication and
/// containing `identity` (which becomes basis element `e_0`).
/// Basis selection: greedy independence scan (identity first).
pub fn FinAlg::subalgebra(
  ambient : FinAlg,
  elems : Array[Array[Int32]],
  identity : Array[Int32],
) -> FinAlg {
  let p = ambient.p
  // sort elements with identity forced first, others ascending
  let sorted = @linalg.elems_normalize(p, elems)
  if !@linalg.elems_contains(sorted, identity) {
    abort("subalgebra: identity not in element set")
  }
  let ordered : Array[Array[Int32]] = [identity]
  for x in sorted {
    if !@linalg.int_arrays_eq(x, identity) {
      ordered.push(x)
    }
  }
  // greedy independent subset spanning everything (identity first)
  let basis : Array[Array[Int32]] = []
  let mut basis_matrix = @linalg.Matrix::zero(p, 0, ambient.dim)
  for x in ordered {
    let rows : Array[Array[Int32]] = []
    for r in basis {
      rows.push(r)
    }
    rows.push(x)
    let cand = @linalg.Matrix::from_rows(p, rows)
    if cand.rank() > basis_matrix.rank() {
      basis.push(x)
      basis_matrix = cand
    }
  }
  // closure: |elems| must be p^basis.length
  if @num.power_int(p, basis.length()) != ordered.length() {
    abort("subalgebra: element set is not spanned by independent basis")
  }
  let d = basis.length()
  let mult : Array[@linalg.Matrix] = []
  for i in 0..<d {
    let mi = @linalg.Matrix::zero(p, d, d)
    for j in 0..<d {
      let prod = ambient.mul_elem(basis[i], basis[j])
      if !@linalg.elems_contains(sorted, prod) {
        abort("subalgebra: set not closed under multiplication")
      }
      let mut idx = -1
      for r in 0..<d {
        if @linalg.int_arrays_eq(basis[r], prod) {
          idx = r
        }
      }
      // product may land outside the independent basis but inside the span:
      // express prod in the basis by solving the linear system
      if idx == -1 {
        // express prod in the basis: matrix COLUMNS = basis vectors
        // (ambient.dim × d), so `bm · α = prod` solves for coefficients
        let bm = @linalg.Matrix::zero(p, ambient.dim, d)
        for c in 0..<d {
          for rr in 0..<ambient.dim {
            bm.data[rr][c] = basis[c][rr]
          }
        }
        match bm.solve(prod) {
          Some(co) =>
            for r in 0..<d {
              mi.data[r][j] = co[r]
            }
          None => abort("subalgebra: product not in span of basis")
        }
      } else {
        mi.data[idx][j] = 1
      }
    }
    mult.push(mi)
  }
  let alg = FinAlg::{ p, dim: d, mult, }
  if !alg.validate() {
    abort("subalgebra: produced structure failed validation")
  }
  alg
}
