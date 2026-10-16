///|
/// All `𝔽_p`-rational points of `𝔸^n` (normalized, lexicographically
/// sorted). Guards `p^n ≤ bound` to keep enumeration honest.
pub fn affine_points(
  p : Int32,
  nvars : Int32,
  bound : Int32,
) -> Array[Array[Int32]] {
  if @num.power_int(p, nvars) > bound {
    abort("affine_points: space too large")
  }
  @linalg.elems_normalize(p, @linalg.enumerate_vectors(p, nvars))
}

///|
/// Evaluate the monomial `x^e` at a point (helper for eval matrices).
fn eval_monomial(p : Int32, e : Array[Int32], pt : Array[Int32]) -> Int32 {
  let mut acc = 1
  for k in 0..<e.length() {
    for _i in 0..<e[k] {
      acc = @num.mul_mod(acc, pt[k], p)
    }
  }
  acc
}

///|
/// The affine variety `V(I) ⊆ 𝔽_p^n`: the common zeros of `gens` among
/// the `𝔽_p`-rational points (definition of an affine algebraic set).
pub fn variety(gens : Array[@poly.Poly], bound : Int32) -> Array[Array[Int32]] {
  if gens.length() == 0 {
    abort("variety: empty generating set (zero ideal)")
  }
  let p = gens[0].modulus
  let nvars = gens[0].nvars
  let pts = affine_points(p, nvars, bound)
  let out : Array[Array[Int32]] = []
  for pt in pts {
    let mut vanishes = true
    for f in gens {
      if f.eval(pt).val != 0 {
        vanishes = false
      }
    }
    if vanishes {
      out.push(pt)
    }
  }
  out
}

///|
/// The linear polynomial `x_i − a` over `𝔽_p`.
fn affine_linear(p : Int32, nvars : Int32, i : Int32, a : Int32) -> @poly.Poly {
  let e1 : Array[Int32] = []
  for _k in 0..<nvars {
    e1.push(0)
  }
  e1[i] = 1
  if @num.mod_pos(a, p) == 0 {
    @poly.poly_of_terms(nvars, p, [(1, e1)])
  } else {
    let zero_e : Array[Int32] = []
    for _k in 0..<nvars {
      zero_e.push(0)
    }
    @poly.poly_of_terms(nvars, p, [(1, e1), (@num.mod_pos(-a, p), zero_e)])
  }
}

///|
/// The vanishing ideal `I(S) = { f : f(a) = 0 ∀ a ∈ S }`, computed as the
/// intersection of the point-maximal ideals `(x_0−a_0, …, x_{n−1}−a_{n−1})`.
/// Theorem: `I(S)` is radical, `V(I(S)) = S`, and the coordinate ring
/// `𝔽_p[x]/I(S)` has dimension exactly `|S|`.
pub fn vanishing_ideal(
  s : Array[Array[Int32]],
  p : Int32,
  nvars : Int32,
) -> @poly.PolyIdeal {
  if s.length() == 0 {
    return @poly.PolyIdeal::unit(nvars, p) // I(∅) = (1)
  }
  let mut acc : @poly.PolyIdeal = @poly.PolyIdeal::unit(nvars, p)
  let mut first = true
  for pt in s {
    let gens : Array[@poly.Poly] = []
    for i in 0..<nvars {
      gens.push(affine_linear(p, nvars, i, pt[i]))
    }
    let mi = @poly.PolyIdeal::new(nvars, p, gens)
    if first {
      acc = mi
      first = false
    } else {
      acc = acc.intersect(mi)
    }
  }
  acc
}

///|
/// The standard monomial basis of `I(S)` with `1` at index 0 — exactly the
/// basis convention used by `FinAlg::zero_dim_quotient`.
pub fn coordinate_basis(
  s : Array[Array[Int32]],
  p : Int32,
  nvars : Int32,
) -> Array[Array[Int32]] {
  let i_s = vanishing_ideal(s, p, nvars)
  match @poly.standard_monomials(i_s.gens) {
    Some(b) => {
      let d = b.length()
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
      let out : Array[Array[Int32]] = []
      for x in b {
        out.push(x)
      }
      if i0 > 0 {
        let t = out[0]
        out[0] = out[i0]
        out[i0] = t
      }
      out
    }
    None => abort("coordinate_basis: variety is infinite (unexpected)")
  }
}

///|
/// The coordinate ring `𝔽_p[x_0..x_{n−1}]/I(S)` (the ring of regular
/// functions on the affine variety `S`) as a finite algebra — `None` when
/// `S = ∅` (the zero ring is not representable).
/// Theorem: `dim_k coord(S) = |S|` (regular functions on `S` ↔ `𝔽_p^S`).
pub fn coordinate_ring(
  s : Array[Array[Int32]],
  p : Int32,
  nvars : Int32,
) -> @finite.FinAlg? {
  if s.length() == 0 {
    return None
  }
  let i_s = vanishing_ideal(s, p, nvars)
  Some(@finite.FinAlg::zero_dim_quotient(p, i_s.gens))
}

///|
/// The evaluation matrix `E[point][basis monomial]` of the coordinate ring
/// basis at the points of `S`. Theorem (CRT / separatedness): `E` has full
/// rank `|S|` ⇔ evaluation `coord(S) → 𝔽_p^S` is a ring isomorphism.
pub fn eval_matrix(
  s : Array[Array[Int32]],
  p : Int32,
  nvars : Int32,
) -> @linalg.Matrix {
  let basis = coordinate_basis(s, p, nvars)
  let m = @linalg.Matrix::zero(p, s.length(), basis.length())
  for a in 0..<s.length() {
    for k in 0..<basis.length() {
      m.data[a][k] = eval_monomial(p, basis[k], s[a])
    }
  }
  m
}

///|
/// Is the evaluation map `coord(S) → 𝔽_p^S` an isomorphism (full rank)?
pub fn crt_iso_holds(s : Array[Array[Int32]], p : Int32, nvars : Int32) -> Bool {
  if s.length() == 0 {
    return false
  }
  let e = eval_matrix(s, p, nvars)
  e.rows == e.cols && e.rank() == s.length()
}

///|
/// 雅可比矩陣（定義）：`J_f(pt) = (∂f_i/∂x_j)(pt)`，行 = 生成元、列 = 變元，
/// 係數取 `rep ∈ 𝔽_p`。粗糙性（singularity）由其秩判定：
/// 仿射曲面在 `pt` 光滑 ⟺ 全體生成元在 `pt` 消失且 `rank J = nvars`。
pub fn jacobian_matrix(
  gens : Array[@poly.Poly],
  pt : Array[Int32],
) -> @linalg.Matrix {
  if gens.length() == 0 {
    abort("jacobian_matrix: empty generating set")
  }
  let nvars = gens[0].nvars
  let p = gens[0].modulus
  let rows : Array[Array[Int32]] = []
  for f in gens {
    if f.nvars != nvars || f.modulus != p {
      abort("jacobian_matrix: inconsistent generators")
    }
    let row : Array[Int32] = []
    for j in 0..<nvars {
      row.push(f.derivative(j).eval(pt).rep())
    }
    rows.push(row)
  }
  @linalg.Matrix::from_rows(p, rows)
}

///|
/// 光滑點判定（定義）：`pt ∈ V(gens)` 且切空間維數等於簇維數
/// `dim T_pt(V) = nvars − rank J(pt) = dim_v`。
/// 定理（光滑 ⟺ 正則）：此條件等價於商環在對應點極大理想處正則
/// `dim_k m/m² = dim V`（嵌入維數 = 幾何維數）。
pub fn smooth_at(
  gens : Array[@poly.Poly],
  pt : Array[Int32],
  dim_v : Int32,
) -> Bool {
  if gens.length() == 0 {
    return false
  }
  let nvars = gens[0].nvars
  for f in gens {
    if f.eval(pt).rep() != 0 {
      return false
    }
  }
  nvars - jacobian_matrix(gens, pt).rank() == dim_v
}

///|
/// 奇異點枚舉（算法）：掃描 `V(gens)` 並保留切空間維數大於 `dim_v` 的點。
/// 定理：奇異軌跡 = `{ pt ∈ V : dim T_pt V > dim_v }`；空 ⟺ 簇光滑。
pub fn singular_points(
  gens : Array[@poly.Poly],
  bound : Int32,
  dim_v : Int32,
) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for pt in variety(gens, bound) {
    if !smooth_at(gens, pt, dim_v) {
      out.push(pt)
    }
  }
  out
}
