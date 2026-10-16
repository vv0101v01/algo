///|
/// Dense matrix over the prime field `𝔽_p`.
/// All entries are kept in the canonical range `[0, p)`.
/// Zero-cost note: this is a plain struct of value data; every operation below
/// is a concrete method (static dispatch, no boxing, no virtual calls).
pub(all) struct Matrix {
  p : Int32
  rows : Int32
  cols : Int32
  data : Array[Array[Int32]]
} derive(Debug)

///|
/// Deep copy of a matrix.
pub fn Matrix::copy(self : Self) -> Matrix {
  let data : Array[Array[Int32]] = []
  for i in 0..<self.rows {
    let row : Array[Int32] = []
    for j in 0..<self.cols {
      row.push(self.data[i][j])
    }
    data.push(row)
  }
  Matrix::{ p: self.p, rows: self.rows, cols: self.cols, data, }
}

///|
/// The zero `rows × cols` matrix over `𝔽_p`.
pub fn Matrix::zero(p : Int32, rows : Int32, cols : Int32) -> Matrix {
  let data : Array[Array[Int32]] = []
  for _i in 0..<rows {
    let row : Array[Int32] = []
    for _j in 0..<cols {
      row.push(0)
    }
    data.push(row)
  }
  Matrix::{ p, rows, cols, data, }
}

///|
/// Build a matrix from raw rows, normalizing every entry into `[0, p)`.
pub fn Matrix::from_rows(p : Int32, rows : Array[Array[Int32]]) -> Matrix {
  let n = rows.length()
  let m = if n == 0 { 0 } else { rows[0].length() }
  let data : Array[Array[Int32]] = []
  for i in 0..<n {
    let row : Array[Int32] = []
    for j in 0..<m {
      row.push(@num.mod_pos(rows[i][j], p))
    }
    data.push(row)
  }
  Matrix::{ p, rows: n, cols: m, data, }
}

///|
/// The `n × n` identity matrix over `𝔽_p`.
pub fn Matrix::identity(p : Int32, n : Int32) -> Matrix {
  let a = Matrix::zero(p, n, n)
  for i in 0..<n {
    a.data[i][i] = 1
  }
  a
}

///|
/// Entry read (0-based).
pub fn Matrix::get(self : Self, i : Int32, j : Int32) -> Int32 {
  self.data[i][j]
}

///|
/// Entry write, normalized modulo `p`.
pub fn Matrix::set(self : Self, i : Int32, j : Int32, v : Int32) -> Unit {
  self.data[i][j] = @num.mod_pos(v, self.p)
}

///|
/// Matrix addition over `𝔽_p`.
pub fn Matrix::add(self : Self, other : Matrix) -> Matrix {
  if self.p != other.p || self.rows != other.rows || self.cols != other.cols {
    abort("Matrix::add: shape or characteristic mismatch")
  }
  let out = Matrix::zero(self.p, self.rows, self.cols)
  for i in 0..<self.rows {
    for j in 0..<self.cols {
      out.data[i][j] = @num.mod_pos(self.data[i][j] + other.data[i][j], self.p)
    }
  }
  out
}

///|
/// Matrix multiplication over `𝔽_p`; accumulates with a reduction per step so
/// no intermediate product can overflow the 32-bit `Int`.
pub fn Matrix::mul(self : Self, other : Matrix) -> Matrix {
  if self.p != other.p || self.cols != other.rows {
    abort("Matrix::mul: shape or characteristic mismatch")
  }
  let out = Matrix::zero(self.p, self.rows, other.cols)
  for i in 0..<self.rows {
    for k in 0..<self.cols {
      let a = self.data[i][k]
      if a != 0 {
        for j in 0..<other.cols {
          let b = other.data[k][j]
          if b != 0 {
            out.data[i][j] = @num.mod_pos(
              out.data[i][j] + @num.mul_mod(a, b, self.p),
              self.p,
            )
          }
        }
      }
    }
  }
  out
}

///|
/// Matrix–vector product; `v` has length `self.cols`, result length `self.rows`.
pub fn Matrix::apply(self : Self, v : Array[Int32]) -> Array[Int32] {
  if v.length() != self.cols {
    abort("Matrix::apply: dimension mismatch")
  }
  let out : Array[Int32] = []
  for i in 0..<self.rows {
    let mut s = 0
    for j in 0..<self.cols {
      s = @num.mod_pos(s + @num.mul_mod(self.data[i][j], v[j], self.p), self.p)
    }
    out.push(s)
  }
  out
}

///|
/// Transpose.
pub fn Matrix::transpose(self : Self) -> Matrix {
  let out = Matrix::zero(self.p, self.cols, self.rows)
  for i in 0..<self.rows {
    for j in 0..<self.cols {
      out.data[j][i] = self.data[i][j]
    }
  }
  out
}

///|
/// Row-swap internal step.
fn swap_rows(m : Matrix, i : Int32, j : Int32) -> Unit {
  if i == j {
    return
  }
  for c in 0..<m.cols {
    let t = m.data[i][c]
    m.data[i][c] = m.data[j][c]
    m.data[j][c] = t
  }
}

///|
/// Gauss–Jordan elimination in row-reduced echelon form.
/// Returns `(R, pivots)` where `pivots[i]` is the pivot column of row `i` and
/// `pivots.length() == rank`. Theorem: `R` is unique for the row space, so
/// `rref(A) == rref(B)` iff `row(A) == row(B)`.
pub fn Matrix::rref(self : Self) -> (Matrix, Array[Int32]) {
  let m = self.copy()
  let p = m.p
  let pivots : Array[Int32] = []
  let mut r = 0
  for c in 0..<m.cols {
    if r >= m.rows {
      break
    }
    let mut piv = -1
    for i in r..<m.rows {
      if m.data[i][c] != 0 {
        piv = i
        break
      }
    }
    if piv == -1 {
      continue
    }
    swap_rows(m, r, piv)
    let inv = @num.invmod(m.data[r][c], p)
    let inv = match inv {
      Some(x) => x
      None => abort("rref: non-invertible pivot in a prime field")
    }
    for j in 0..<m.cols {
      m.data[r][j] = @num.mul_mod(m.data[r][j], inv, p)
    }
    for i in 0..<m.rows {
      if i != r {
        let f = m.data[i][c]
        if f != 0 {
          for j in 0..<m.cols {
            let sub = @num.mul_mod(f, m.data[r][j], p)
            let v = m.data[i][j] - sub
            m.data[i][j] = if v < 0 { v + p } else { v }
          }
        }
      }
    }
    pivots.push(c)
    r = r + 1
  }
  (m, pivots)
}

///|
/// Rank of the matrix (= number of pivots in its RREF).
pub fn Matrix::rank(self : Self) -> Int32 {
  let (_, pivots) = self.rref()
  pivots.length()
}

///|
/// A basis of the kernel of the linear map `x ↦ self · x` over `𝔽_p`.
/// Each returned vector has length `self.cols`. Theorem: `dim ker + rank = cols`.
pub fn Matrix::nullspace(self : Self) -> Array[Array[Int32]] {
  let (r, pivots) = self.rref()
  let is_pivot : Array[Bool] = []
  for _j in 0..<self.cols {
    is_pivot.push(false)
  }
  for c in pivots {
    is_pivot[c] = true
  }
  let out : Array[Array[Int32]] = []
  for f in 0..<self.cols {
    if is_pivot[f] {
      continue
    }
    let v : Array[Int32] = []
    for _j in 0..<self.cols {
      v.push(0)
    }
    v[f] = 1
    for i in 0..<pivots.length() {
      // row i: x_pivot + Σ_j R[i][j] x_j = 0, free vars except f are 0
      let neg = r.data[i][f] // = -v[f] coefficient, pivot entry normalized to 1
      v[pivots[i]] = if neg == 0 { 0 } else { r.p - neg }
    }
    out.push(v)
  }
  out
}

///|
/// Solve the linear system `self · x = b` over `𝔽_p`; returns one particular
/// solution with free variables set to 0, or `None` if the system is
/// inconsistent. Algorithm: Gauss–Jordan on the augmented matrix.
pub fn Matrix::solve(self : Self, b : Array[Int32]) -> Array[Int32]? {
  if b.length() != self.rows {
    return None
  }
  let p = self.p
  // augmented matrix: cols + 1 columns, pivots searched only in real columns
  let m = Matrix::zero(p, self.rows, self.cols + 1)
  for i in 0..<self.rows {
    for j in 0..<self.cols {
      m.data[i][j] = self.data[i][j]
    }
    m.data[i][self.cols] = @num.mod_pos(b[i], p)
  }
  let pivots : Array[Int32] = []
  let mut r = 0
  for c in 0..<self.cols {
    if r >= m.rows {
      break
    }
    let mut piv = -1
    for i in r..<m.rows {
      if m.data[i][c] != 0 {
        piv = i
        break
      }
    }
    if piv == -1 {
      continue
    }
    swap_rows(m, r, piv)
    let inv = match @num.invmod(m.data[r][c], p) {
      Some(x) => x
      None => abort("solve: non-invertible pivot in a prime field")
    }
    for j in 0..<(self.cols + 1) {
      m.data[r][j] = @num.mul_mod(m.data[r][j], inv, p)
    }
    for i in 0..<m.rows {
      if i != r {
        let f = m.data[i][c]
        if f != 0 {
          for j in 0..<(self.cols + 1) {
            let sub = @num.mul_mod(f, m.data[r][j], p)
            let v = m.data[i][j] - sub
            m.data[i][j] = if v < 0 { v + p } else { v }
          }
        }
      }
    }
    pivots.push(c)
    r = r + 1
  }
  // consistency: a row with zero coefficient part must have zero RHS
  for i in 0..<m.rows {
    let mut all_zero = true
    for j in 0..<self.cols {
      if m.data[i][j] != 0 {
        all_zero = false
      }
    }
    if all_zero && m.data[i][self.cols] != 0 {
      return None
    }
  }
  let x : Array[Int32] = []
  for _j in 0..<self.cols {
    x.push(0)
  }
  for i in 0..<pivots.length() {
    x[pivots[i]] = m.data[i][self.cols]
  }
  Some(x)
}

///|
/// Does the row space of `self` contain every row of `other`?
/// Theorem: for equal shapes over `𝔽_p`, this holds iff `row(other) ⊆ row(self)`.
pub fn Matrix::rowspace_contains(self : Self, other : Matrix) -> Bool {
  if self.p != other.p || self.cols != other.cols {
    return false
  }
  let (r, pivots) = self.rref()
  for i in 0..<other.rows {
    let row : Array[Int32] = []
    for j in 0..<other.cols {
      row.push(other.data[i][j])
    }
    // reduce `row` against the pivots of rref(self)
    for pi in 0..<pivots.length() {
      let c = pivots[pi]
      let f = row[c]
      if f != 0 {
        for j in 0..<other.cols {
          let sub = @num.mul_mod(f, r.data[pi][j], self.p)
          let v = row[j] - sub
          row[j] = if v < 0 { v + self.p } else { v }
        }
      }
    }
    for j in 0..<other.cols {
      if row[j] != 0 {
        return false
      }
    }
  }
  true
}

///|
/// Canonical flattened RREF (row-major, only pivot rows): two subspaces have
/// equal signatures iff they are equal. Signature length is
/// `rank * cols`; the zero subspace has the empty signature.
pub fn Matrix::rref_signature(self : Self) -> Array[Int32] {
  let (r, pivots) = self.rref()
  let out : Array[Int32] = []
  for i in 0..<pivots.length() {
    for j in 0..<self.cols {
      out.push(r.data[i][j])
    }
  }
  out
}

///|
/// Structural equality of two integer arrays.
pub fn int_arrays_eq(a : Array[Int32], b : Array[Int32]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if a[i] != b[i] {
      return false
    }
  }
  true
}
