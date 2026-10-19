///|
/// 規範形式（normal forms）總集 —— 每種形式附定義、存在/唯一性定理與演算法。
///
/// 本檔交付六件套：
///   1. `det_gf`        —— 𝔽_p 上行列式（Gauss 消去）
///   2. `mat_charpoly`  —— 特徵多項式 χ_A(t) = det(tI − A)（插值法）
///   3. `snf_int`       —— ℤ 上 Smith 規範形式（初等行列/行/列變換）
///   4. `hnf_int`       —— ℤ 上 Hermite 規範形式（行式）
///   5. `rational_canonical_form` —— 𝔽_p 上有理標準形（Frobenius 標準形）
///   6. `anf_*`         —— GF(2) 布爾函數代數標準形（Möbius 變換 / Reed–Muller 展開）
///
/// 證明方式與本庫一致：定理寫成 doc（公式 + 語義），正確性由
/// **憑證測試**（U·A·V = D、det U = ±1）與 **不變量性質測試**
/// （χ 相似不變、Cayley–Hamilton、d_i | d_{i+1}、往返同構）給出計算證據；
/// `verify/` 的形式化目標獨立於此（`moon prove`）。
///
/// 例外聲明：ℤ 規範形式（HNF/SNF/det_int）工作在 ℤ 上，其內部除法
/// `a / b`、餘數 `a % b` 是**截斷語義**（Euclidean 餘數 |r| < |b|），
/// 這正是 ℤ 歐幾里得整環的演算要求 —— 與 `@num.mod_pos`（同餘代表）不同，
/// 此處不作模正規化，屬刻意保留。

///==========================================================================
/// 1. 𝔽_p 行列式
///==========================================================================

///|
/// Gauss 消去求 `det(A)`（A 方陣，素數模 `p`）。
///
/// 定義：行列式為列線性交替多線性型；演算法以上三角化為主線 ——
/// 每步選主元 `v`（非零），`det ← v·det`（模 p），以 `v⁻¹` 消去下方；
/// 列交換翻轉符号。複雜度 `O(n³)`。
///
/// 定理（正確性）：初等行變換中「加法倍數」保行列式、「交換」變號、
/// 上三角陣行列式為對角積 —— 故回溯得 det，且 `det(A·B) = det A · det B`
/// （以性質測試驗證）。
pub fn det_gf(a : @linalg.Matrix) -> Int32 {
  let p = a.p
  let n = a.rows
  if n != a.cols {
    abort("det_gf: matrix must be square")
  }
  // 抽出行 → 單一消去實現（det_gf_of，零重複）
  let rows : Array[Array[Int32]] = []
  for i in 0..<n {
    let row : Array[Int32] = []
    for j in 0..<n {
      row.push(@num.mod_pos(a.data[i][j], p))
    }
    rows.push(row)
  }
  det_gf_of(p, n, rows)
}

///==========================================================================
/// 2. 特徵多項式
///==========================================================================

///|
/// 稠密一元多項式（mod p）的升冪係數 `c_0 + c_1 t + … + c_d t^d`。
/// 規範：係數 ∈ [0, p)，**無尾零**；零多項式以空數組 `[]` 表示。
fn up_norm(p : Int32, a : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for x in a {
    out.push(@num.mod_pos(x, p))
  }
  while out.length() > 0 && out[out.length() - 1] == 0 {
    let _ = out.pop()
  }
  out
}

///|
/// 一元多項式加法（升冪稠密，模 p）。
fn up_add(p : Int32, a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let n = if a.length() > b.length() { a.length() } else { b.length() }
  let out : Array[Int32] = []
  for i in 0..<n {
    let x = if i < a.length() { a[i] } else { 0 }
    let y = if i < b.length() { b[i] } else { 0 }
    out.push(x + y)
  }
  up_norm(p, out)
}

///|
/// 一元多項式取負（模 p）。
fn up_neg(p : Int32, a : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for x in a {
    out.push(-x)
  }
  up_norm(p, out)
}

///|
/// 一元多項式乘法：稠密卷積，`O(deg a · deg b)`。
fn up_mul(p : Int32, a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  if a.length() == 0 || b.length() == 0 {
    return []
  }
  let d = a.length() + b.length() - 2
  let out : Array[Int32] = []
  for _k in 0..<(d + 1) {
    out.push(0)
  }
  for i in 0..<a.length() {
    for j in 0..<b.length() {
      let prod = @num.mul_mod(a[i], b[j], p)
      out[i + j] = @num.mod_pos(out[i + j] + prod, p)
    }
  }
  up_norm(p, out)
}

///|
/// 一元多項式乘常數（模 p）。
fn up_scale(p : Int32, c : Int32, a : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for x in a {
    out.push(@num.mul_mod(c, x, p))
  }
  up_norm(p, out)
}

///|
/// 帶餘除法 `a = q·b + r`，`deg r < deg b`（素數模 p，b ≠ 0）。
/// 歐幾里得整環 𝔽_p[t] 的演算核心；回 `(q, r)`。
fn up_divmod(
  p : Int32,
  a : Array[Int32],
  b : Array[Int32],
) -> (Array[Int32], Array[Int32]) {
  if b.length() == 0 {
    abort("up_divmod: division by zero polynomial")
  }
  let db = b.length() - 1
  let lc = b[db]
  let inv = match @num.invmod(lc, p) {
    Some(v) => v
    None => abort("up_divmod: leading coefficient not invertible")
  }
  let ra = up_norm(p, a)
  if ra.length() == 0 || ra.length() - 1 < db {
    return ([], ra)
  }
  let da = ra.length() - 1
  // 固定長度工作拷貝：自上而下把位置 db+k 的係數消成 0
  let r : Array[Int32] = []
  for x in ra {
    r.push(x)
  }
  let q : Array[Int32] = []
  for _k in 0..<(da - db + 1) {
    q.push(0)
  }
  let mut k = da - db
  while k >= 0 {
    let top = r[db + k]
    if top != 0 {
      let coef = @num.mul_mod(top, inv, p)
      q[k] = coef
      let mut i = 0
      while i <= db {
        let sub = @num.mul_mod(coef, b[i], p)
        r[k + i] = @num.mod_pos(r[k + i] - sub, p)
        i = i + 1
      }
    }
    k = k - 1
  }
  // 剝尾零
  while r.length() > 0 && r[r.length() - 1] == 0 {
    let _ = r.pop()
  }
  while q.length() > 0 && q[q.length() - 1] == 0 {
    let _ = q.pop()
  }
  (q, r)
}

///|
/// 整除判定：`b | a`（素數模 p；零多項式整除且僅整除零）。
fn up_divides(p : Int32, b : Array[Int32], a : Array[Int32]) -> Bool {
  if a.length() == 0 {
    return true
  }
  if b.length() == 0 {
    return false
  }
  let (_, r) = up_divmod(p, a, b)
  r.length() == 0
}

///|
/// 首一化（monic normalize）：乘首項係數的逆。零多項式原樣返回。
fn up_monic(p : Int32, a : Array[Int32]) -> Array[Int32] {
  if a.length() == 0 {
    return a
  }
  let lc = a[a.length() - 1]
  let inv = match @num.invmod(lc, p) {
    Some(v) => v
    None => abort("up_monic: leading coefficient not invertible")
  }
  up_scale(p, inv, a)
}

///|
/// 多項式求值（Horner，模 p）：`a(x) ∈ 𝔽_p`。
/// 用於特徵多項式的插值一致性檢驗（測試：`χ(x) = det(xI − A)`）。
pub fn up_eval(p : Int32, a : Array[Int32], x : Int32) -> Int32 {
  let mut acc = 0
  let mut i = a.length()
  while i > 0 {
    acc = @num.mul_mod(acc, x, p)
    acc = @num.mod_pos(acc + a[i - 1], p)
    i = i - 1
  }
  acc
}

///|
/// 定義（特徵多項式）：`χ_A(t) = det(t·I − A) ∈ 𝔽_p[t]`，首一 `n` 次。
///
/// 演算法：**插值** —— 在 `t = 0,1,…,n`（`n+1 < p` 個互異點）求
/// `det(tI − A)`（Gauss 消去），Lagrange 插值還原唯一 `n` 次多項式。
/// 輸出升冪係數 `[a_0, …, a_n]`（`a_n = 1`）。
///
/// 定理（Cayley–Hamilton）：`χ_A(A) = 0`（矩陣多項式求值，見
/// `mat_poly_eval`）—— 由性質測試對隨機矩陣驗證。
/// 定理（相似不變量）：A ~ B ⇒ χ_A = χ_B；`tr A = −a_{n−1}`、
/// `det A = (−1)^n a_0`。
pub fn mat_charpoly(a : @linalg.Matrix) -> Array[Int32] {
  let p = a.p
  let n = a.rows
  if n != a.cols {
    abort("mat_charpoly: matrix must be square")
  }
  if n == 0 {
    abort("mat_charpoly: empty matrix")
  }
  if p <= n {
    abort("mat_charpoly: need p > n for n+1 distinct evaluation points")
  }
  // 求值 y_i = χ(i)，i = 0..n
  let ys : Array[Int32] = []
  for i in 0..<(n + 1) {
    // det(i·I − A)
    let m : Array[Array[Int32]] = []
    for r in 0..<n {
      let row : Array[Int32] = []
      for c in 0..<n {
        let diag = if r == c { i } else { 0 }
        row.push(@num.mod_pos(diag - a.data[r][c], p))
      }
      m.push(row)
    }
    ys.push(det_gf_of(p, n, m))
  }
  // Lagrange: χ = Σ y_i · Π_{j≠i} (t − x_j) / Π_{j≠i} (x_i − x_j)
  let mut chi : Array[Int32] = []
  for i in 0..<(n + 1) {
    // basis_i = Π_{j≠i} (t − j)
    let mut basis : Array[Int32] = [1]
    for j in 0..<(n + 1) {
      if j != i {
        // 乘 (t − j)
        basis = up_mul(p, basis, [@num.mod_pos(-j, p), 1])
      }
    }
    // 分母 = Π_{j≠i} (i − j) mod p
    let mut den = 1
    for j in 0..<(n + 1) {
      if j != i {
        den = @num.mul_mod(den, i - j, p)
      }
    }
    let dinv = match @num.invmod(den, p) {
      Some(v) => v
      None => abort("mat_charpoly: duplicate interpolation nodes")
    }
    let coef = @num.mul_mod(ys[i], dinv, p)
    chi = up_add(p, chi, up_scale(p, coef, basis))
  }
  chi
}

///|
/// `det_gf` 的數組版（供 `mat_charpoly` 內部使用；公開入口仍是 Matrix 版）。
fn det_gf_of(p : Int32, n : Int32, m : Array[Array[Int32]]) -> Int32 {
  let mut det = 1
  let mat = m
  for c in 0..<n {
    let mut piv = -1
    for i in c..<n {
      if mat[i][c] != 0 {
        piv = i
      }
    }
    if piv == -1 {
      return 0
    }
    if piv != c {
      let tmp = mat[piv]
      mat[piv] = mat[c]
      mat[c] = tmp
      det = @num.mod_pos(-det, p)
    }
    let lead = mat[c][c]
    det = @num.mul_mod(det, lead, p)
    let inv = match @num.invmod(lead, p) {
      Some(v) => v
      None => abort("det_gf_of: pivot not invertible")
    }
    for i in (c + 1)..<n {
      if mat[i][c] != 0 {
        let q = @num.mul_mod(mat[i][c], inv, p)
        for j in c..<n {
          let sub = @num.mul_mod(q, mat[c][j], p)
          mat[i][j] = @num.mod_pos(mat[i][j] - sub, p)
        }
      }
    }
  }
  det
}

///|
/// 矩陣多項式求值（Horner）：`Σ a_i · A^i`，`a_i` 為升冪係數。
/// 用於 Cayley–Hamilton 檢驗 `χ_A(A) = 0`。
pub fn mat_poly_eval(
  coeffs : Array[Int32],
  a : @linalg.Matrix,
) -> @linalg.Matrix {
  let n = a.rows
  if n != a.cols {
    abort("mat_poly_eval: matrix must be square")
  }
  let mut acc = @linalg.Matrix::zero(a.p, n, n)
  let mut i = coeffs.length()
  while i > 0 {
    acc = acc.mul(a)
    // acc ← acc + c·I（c = 下一低次係數）
    let c = coeffs[i - 1]
    if c != 0 {
      for r in 0..<n {
        acc.data[r][r] = @num.mod_pos(acc.data[r][r] + c, a.p)
      }
    }
    i = i - 1
  }
  acc
}

///==========================================================================
/// 3. ℤ 上 Smith 規範形式
///==========================================================================

///|
/// ℤ 的截斷商（SNF 約化用）：`a = q·b + r`，`|r| < |b|` —— 演算法只消費
/// 商 `q`（行/列變換 `row −= q·pivot` 後的餘數直接由被減結果讀取）。
fn iquo(a : Int32, b : Int32) -> Int32 {
  if b == 0 {
    abort("iquo: division by zero")
  }
  a / b
}

///|
/// 整數方陣行列式（Laplace 展開）。**僅限小矩陣**（測試憑證用：
/// `det(U) = ±1` 驗證幺模性；輸入約束：n ≤ 5、元素適度，避免 Int32 溢出）。
pub fn det_int(a : Array[Array[Int32]]) -> Int32 {
  let n = a.length()
  if n == 0 {
    return 1
  }
  if a[0].length() != n {
    abort("det_int: matrix must be square")
  }
  if n == 1 {
    return a[0][0]
  }
  let mut det = 0
  for j in 0..<n {
    if a[0][j] == 0 {
      continue
    }
    let minor : Array[Array[Int32]] = []
    for i in 1..<n {
      let row : Array[Int32] = []
      for k in 0..<n {
        if k != j {
          row.push(a[i][k])
        }
      }
      minor.push(row)
    }
    let m = det_int(minor)
    if @num.mod_pos(j, 2) == 0 {
      det = det + a[0][j] * m
    } else {
      det = det - a[0][j] * m
    }
  }
  det
}

///|
/// 定義（Smith 規範形式）：對 `A ∈ ℤ^{m×n}`，存在幺模 `U ∈ ℤ^{m×m}`、
/// `V ∈ ℤ^{n×n}` 與對角 `D = diag(d_1, …, d_r, 0, …)` 使
/// **U·A·V = D**，且 `d_i ≥ 0`、`d_i | d_{i+1}`。
///
/// 定理（存在唯一性）：(i) 上式恆可達（演算法：對 (k,k) 位置反覆
/// ① 行/列 Euclidean 約化至餘數 ② 若餘數非零則交換入主元（絕對值嚴降，
/// 有限步終止）③ 若主元不整除子矩陣某元素，列消去後交換把更小餘數送入
/// 主元 —— 終止時 `d_k` 整除整個剩餘子矩陣）；(ii) `d_1 | d_2 | …` 且
/// `d_1⋯d_k` = 所有 k 階子式之 gcd（不變量 —— 故對角唯一）。
/// 模 `ℤ^n / A ℤ^m`（有限生成 Abel 群基本定理）：≅ ⊕ ℤ/d_i。
///
/// 輸出 `(diag, U, V)`；憑證 `U·A·V = diag`、`det U = ±1`、`det V = ±1`
/// 由測試給出。輸入約束：小矩陣（n, m ≤ 5、元素適度）防 Int32 溢出。
pub fn snf_int(
  a : Array[Array[Int32]],
) -> (Array[Int32], Array[Array[Int32]], Array[Array[Int32]]) {
  let m = a.length()
  if m == 0 {
    abort("snf_int: empty matrix")
  }
  let n = a[0].length()
  if n == 0 {
    abort("snf_int: empty matrix")
  }
  // D ← A 深拷貝；U、V 初等變換追蹤
  let d : Array[Array[Int32]] = []
  for i in 0..<m {
    let row : Array[Int32] = []
    for j in 0..<n {
      row.push(a[i][j])
    }
    d.push(row)
  }
  let u : Array[Array[Int32]] = []
  for i in 0..<m {
    let row : Array[Int32] = []
    for j in 0..<m {
      row.push(if i == j { 1 } else { 0 })
    }
    u.push(row)
  }
  let v : Array[Array[Int32]] = []
  for i in 0..<n {
    let row : Array[Int32] = []
    for j in 0..<n {
      row.push(if i == j { 1 } else { 0 })
    }
    v.push(row)
  }
  let mut steps = 0
  let mut t = 0
  while t < m && t < n {
    // 1) 非零元換入 (t,t)
    if d[t][t] == 0 {
      let mut pi = -1
      let mut pj = -1
      for i in t..<m {
        for j in t..<n {
          if d[i][j] != 0 {
            pi = i
            pj = j
          }
        }
      }
      if pi == -1 {
        break // 子矩陣全零 → 完成
      }
      let tmp = d[pi]
      d[pi] = d[t]
      d[t] = tmp
      let tu = u[pi]
      u[pi] = u[t]
      u[t] = tu
      for r in 0..<n {
        let x = v[r][pj]
        v[r][pj] = v[r][t]
        v[r][t] = x
      }
      for r in 0..<m {
        let x = d[r][pj]
        d[r][pj] = d[r][t]
        d[r][t] = x
      }
    }
    // 2) 內層：主元約化至整除整個子矩陣
    let mut ok = false
    while !ok {
      steps = steps + 1
      if steps > 20000 {
        abort("snf_int: iteration guard tripped")
      }
      // 2a. 列 t 下方清零（行 Euclidean 約化，餘數非零則換入主元）
      let mut restart = false
      for i in (t + 1)..<m {
        if d[i][t] != 0 {
          let q = iquo(d[i][t], d[t][t])
          if q != 0 {
            for c in 0..<n {
              d[i][c] = d[i][c] - q * d[t][c]
            }
            for c in 0..<m {
              u[i][c] = u[i][c] - q * u[t][c]
            }
          }
          if d[i][t] != 0 {
            let tmp = d[t]
            d[t] = d[i]
            d[i] = tmp
            let tu = u[t]
            u[t] = u[i]
            u[i] = tu
            restart = true
            break
          }
        }
      }
      if restart {
        continue
      }
      // 2b. 行 t 右方清零（列 Euclidean 約化）
      for j in (t + 1)..<n {
        if d[t][j] != 0 {
          let q = iquo(d[t][j], d[t][t])
          if q != 0 {
            for r in 0..<m {
              d[r][j] = d[r][j] - q * d[r][t]
            }
            for r in 0..<n {
              v[r][j] = v[r][j] - q * v[r][t]
            }
          }
          if d[t][j] != 0 {
            for r in 0..<m {
              let x = d[r][t]
              d[r][t] = d[r][j]
              d[r][j] = x
            }
            for r in 0..<n {
              let x = v[r][t]
              v[r][t] = v[r][j]
              v[r][j] = x
            }
            restart = true
            break
          }
        }
      }
      if restart {
        continue
      }
      // 2c. 主元必須整除子矩陣全部元素；否則把更小餘數送入主元
      let mut bi = -1
      let mut bj = -1
      for i in (t + 1)..<m {
        for j in (t + 1)..<n {
          // ℤ 整除判定：`x % d == 0` 對任意符號等價於 d | x（刻意用裸 %）
          if d[i][j] % d[t][t] != 0 {
            bi = i
            bj = j
          }
        }
      }
      if bi == -1 {
        ok = true
      } else {
        let q = iquo(d[bi][bj], d[t][t])
        if q != 0 {
          for r in 0..<m {
            d[r][bj] = d[r][bj] - q * d[r][t]
          }
          for r in 0..<n {
            v[r][bj] = v[r][bj] - q * v[r][t]
          }
        }
        // 交換：行 (t, bi) → 再列 (t, bj)（見定理演算法）
        let tmp = d[t]
        d[t] = d[bi]
        d[bi] = tmp
        let tu = u[t]
        u[t] = u[bi]
        u[bi] = tu
        for r in 0..<m {
          let x = d[r][t]
          d[r][t] = d[r][bj]
          d[r][bj] = x
        }
        for r in 0..<n {
          let x = v[r][t]
          v[r][t] = v[r][bj]
          v[r][bj] = x
        }
      }
    }
    t = t + 1
  }
  // 規範化：主元非負（行變號 → U 行同時變號）
  let diag : Array[Int32] = []
  let lim_s = if m < n { m } else { n }
  for i in 0..<lim_s {
    if d[i][i] < 0 {
      for c in 0..<n {
        d[i][c] = -d[i][c]
      }
      for c in 0..<m {
        u[i][c] = -u[i][c]
      }
    }
    diag.push(d[i][i])
  }
  (diag, u, v)
}

///==========================================================================
/// 4. ℤ 上 Hermite 規範形式（行式）
///==========================================================================

///|
/// 向下取整除法的餘數：回 `r ∈ [0, b)`（b > 0）。
fn floor_mod_pos(a : Int32, b : Int32) -> Int32 {
  if b <= 0 {
    abort("floor_mod_pos: modulus must be positive")
  }
  let r = a % b
  if r < 0 {
    r + b
  } else {
    r
  }
}

///|
/// 定義（行式 Hermite 規範形式）：`H = T·A`，`T ∈ ℤ^{m×m}` 幺模（`det T = ±1`），
/// 滿足
///   (行 echelon) 每行首個非零元（主元）左側全零，主元列指標嚴格遞增；
///   (正主元)    主元 > 0；
///   (列約化)    每個主元列中，主元**上方**的元素 ∈ [0, 主元)。
///
/// 定理（存在唯一）：(i) 演算法 —— 逐列：`egcd` 二行幺模組合把 gcd 送入
/// 主元並清零下方，主元取正；完成後對每個主元列把上方元素取模約化
/// （向上行減主元行倍數不破壞 echelon：主元行在更早列全零）。
/// (ii) 唯一性 —— 「上方取模」封閉了行組合自由度：設 H、H' 皆合規且
/// 行等價，差倍數必落在主元列 → 取模後為 0。
/// H 的行生成與 A 相同的格（lattice）；憑證 `T·A = H`、`det T = ±1`。
///
/// 輸出 `(H, T)`。輸入約束同 `snf_int`（小矩陣防 Int32 溢出）。
pub fn hnf_int(
  a : Array[Array[Int32]],
) -> (Array[Array[Int32]], Array[Array[Int32]]) {
  let m = a.length()
  if m == 0 {
    abort("hnf_int: empty matrix")
  }
  let n = a[0].length()
  if n == 0 {
    abort("hnf_int: empty matrix")
  }
  let h : Array[Array[Int32]] = []
  for i in 0..<m {
    let row : Array[Int32] = []
    for j in 0..<n {
      row.push(a[i][j])
    }
    h.push(row)
  }
  let tmat : Array[Array[Int32]] = []
  for i in 0..<m {
    let row : Array[Int32] = []
    for j in 0..<m {
      row.push(if i == j { 1 } else { 0 })
    }
    tmat.push(row)
  }
  let mut r = 0
  for c in 0..<n {
    if r >= m {
      break
    }
    // 找 (r.., c) 非零元換入第 r 行
    let mut piv = -1
    for i in r..<m {
      if h[i][c] != 0 {
        piv = i
      }
    }
    if piv == -1 {
      continue // 此列無主元（跳過列）
    }
    if piv != r {
      let tmp = h[piv]
      h[piv] = h[r]
      h[r] = tmp
      let tt = tmat[piv]
      tmat[piv] = tmat[r]
      tmat[r] = tt
    }
    // 逐行 egcd 組合清零下方
    for i in (r + 1)..<m {
      if h[i][c] != 0 {
        let aa = h[r][c]
        let bb = h[i][c]
        let (g, s, tt) = @num.egcd(aa, bb)
        if g == 0 {
          abort("hnf_int: unexpected gcd 0")
        }
        // 2×2 幺模 [[s, tt], [−b/g, a/g]]（det = (s·a + t·b)/g = 1）
        let u11 = s
        let u12 = tt
        let u21 = -bb / g
        let u22 = aa / g
        for j in 0..<n {
          let x = h[r][j]
          let y = h[i][j]
          h[r][j] = u11 * x + u12 * y
          h[i][j] = u21 * x + u22 * y
        }
        for j in 0..<m {
          let x = tmat[r][j]
          let y = tmat[i][j]
          tmat[r][j] = u11 * x + u12 * y
          tmat[i][j] = u21 * x + u22 * y
        }
      }
    }
    if h[r][c] < 0 {
      for j in 0..<n {
        h[r][j] = -h[r][j]
      }
      for j in 0..<m {
        tmat[r][j] = -tmat[r][j]
      }
    }
    r = r + 1
  }
  // 列約化：每個主元列，上方元素取模 ∈ [0, pivot)
  // 重新掃描主元（echelon 結構）
  let mut prow = 0
  for c in 0..<n {
    if prow >= m {
      break
    }
    if h[prow][c] == 0 {
      continue
    }
    // 是主元列（prow 行首個非零在 c 嗎？—— echelon 掃描：
    // 若該行首非零列 = c 則為主元列）
    let mut first = -1
    for j in 0..<n {
      if h[prow][j] != 0 {
        first = j
        break
      }
    }
    if first != c {
      continue // 首非零不在 c → 非主元列（prow 不前進的列已被上面跳過）
    }
    let pivot = h[prow][c]
    for i in 0..<prow {
      let rr = floor_mod_pos(h[i][c], pivot)
      let sub = h[i][c] - rr // floor 商 × pivot
      if sub != 0 {
        let qf = sub / pivot // 精確（sub 是 pivot 的倍數）
        for j in c..<n {
          h[i][j] = h[i][j] - qf * h[prow][j]
        }
        for j in 0..<m {
          tmat[i][j] = tmat[i][j] - qf * tmat[prow][j]
        }
      }
    }
    prow = prow + 1
  }
  (h, tmat)
}

///==========================================================================
/// 5. 𝔽_p 上有理標準形（Rational / Frobenius normal form）
///==========================================================================

///|
/// 伴隨矩陣（companion matrix）：`f = t^d + c_{d−1} t^{d−1} + … + c_0`
/// （升冪 `[c_0, …, c_{d−1}, 1]`，d ≥ 1）的
/// `C(f) = [ e_{i+1} (次對角 1) | 末列 −c_i ]`：
/// `C[i][d−1] = −c_i`、`C[i][i−1] = 1 (i ≥ 1)`、餘 0。
///
/// 定理：`χ_{C(f)} = f`（d = 1,2,3 手算 + 性質測試驗證）。
pub fn companion_matrix(
  p : Int32,
  coeffs : Array[Int32],
) -> Array[Array[Int32]] {
  let f = up_monic(p, up_norm(p, coeffs))
  if f.length() < 2 {
    abort("companion_matrix: need degree >= 1 (monic non-constant)")
  }
  let d = f.length() - 1
  let c : Array[Array[Int32]] = []
  for _i in 0..<d {
    let row : Array[Int32] = []
    for _j in 0..<d {
      row.push(0)
    }
    c.push(row)
  }
  for i in 0..<d {
    c[i][d - 1] = @num.mod_pos(-f[i], p)
    if i >= 1 {
      c[i][i - 1] = 1
    }
  }
  c
}

///|
/// 定義（有理標準形）：設 `A ∈ 𝔽_p^{n×n}`，對 `tI − A ∈ 𝔽_p[t]^{n×n}` 取
/// Smith 形得不變因子（首一）`s_1 | s_2 | … | s_n`（常數者略去），
/// 則 **RCF(A) = C(s_1) ⊕ C(s_2) ⊕ …**（直和 = 分塊對角）。
///
/// 定理（存在唯一）：A 相似於唯一（至塊排序）的 RCF；
/// `χ_A = ∏ s_i`；`𝔽_p[t]`-模 `𝔽_p^n（經 A）` ≅ ⊕ 𝔽_p[t]/(s_i)。
/// 演算法：`snf_upoly(tI − A)` → 伴隨塊直和。
/// 驗證：χ 不變、`tr(A^k)` 相似不變量（k = 1..n）、`d_i | d_{i+1}`、
/// Cayley–Hamilton（由測試給出計算證據）。
///
/// 輸出不變因子（升冪首一係數，按整除鏈排列）與 RCF 矩陣。
pub fn rational_canonical_form(
  a : @linalg.Matrix,
) -> (Array[Array[Int32]], @linalg.Matrix) {
  let p = a.p
  let n = a.rows
  if n != a.cols {
    abort("rational_canonical_form: matrix must be square")
  }
  if n == 0 {
    abort("rational_canonical_form: empty matrix")
  }
  // 構造 tI − A（一元多項式矩陣）
  let mat : Array[Array[Array[Int32]]] = []
  for i in 0..<n {
    let row : Array[Array[Int32]] = []
    for j in 0..<n {
      if i == j {
        // t − a_ii → [−a_ii, 1]
        row.push(up_norm(p, [@num.mod_pos(-a.data[i][j], p), 1]))
      } else {
        row.push(up_norm(p, [-a.data[i][j]]))
      }
    }
    mat.push(row)
  }
  let factors = snf_upoly(p, mat)
  // 分塊對角：每塊 = 非常數 s_i 的伴隨矩陣
  let rcf = @linalg.Matrix::zero(p, n, n)
  let mut off = 0
  for s in factors {
    let d = s.length() - 1 // 常數因子（d=0）→ 略過
    if d >= 1 {
      let block = companion_matrix(p, s)
      for i in 0..<d {
        for j in 0..<d {
          rcf.data[off + i][off + j] = block[i][j]
        }
      }
      off = off + d
    }
  }
  if off != n {
    abort("rational_canonical_form: invariant factor degrees must sum to n")
  }
  (factors, rcf)
}

///|
/// `𝔽_p[t]` 上 Smith 形：輸入一元多項式矩陣，輸出首一不變因子對角
/// （整除鏈 `s_1 | … | s_n`，含常數 1）。演算法同 `snf_int`，以
/// `up_divmod` 的 Euclidean 餘數代替整數餘數（`deg` 嚴降保證終止）。
fn snf_upoly(p : Int32, a : Array[Array[Array[Int32]]]) -> Array[Array[Int32]] {
  let m = a.length()
  if m == 0 {
    abort("snf_upoly: empty matrix")
  }
  let n = a[0].length()
  if n == 0 {
    abort("snf_upoly: empty matrix")
  }
  let d : Array[Array[Array[Int32]]] = []
  for i in 0..<m {
    let row : Array[Array[Int32]] = []
    for j in 0..<n {
      row.push(up_norm(p, a[i][j]))
    }
    d.push(row)
  }
  // 多項式「乘行/列標量」與清零所需的行/列變換
  let mut steps = 0
  let mut t = 0
  while t < m && t < n {
    // 1) 非零元換入 (t,t)
    if d[t][t].length() == 0 {
      let mut pi = -1
      let mut pj = -1
      for i in t..<m {
        for j in t..<n {
          if d[i][j].length() != 0 {
            pi = i
            pj = j
          }
        }
      }
      if pi == -1 {
        break
      }
      let tmp = d[pi]
      d[pi] = d[t]
      d[t] = tmp
      for r in 0..<m {
        let x = d[r][pj]
        d[r][pj] = d[r][t]
        d[r][t] = x
      }
    }
    let mut ok = false
    while !ok {
      steps = steps + 1
      if steps > 20000 {
        abort("snf_upoly: iteration guard tripped")
      }
      // 2a. 列 t 下方清零
      let mut restart = false
      for i in (t + 1)..<m {
        if d[i][t].length() != 0 {
          let (q, _r) = up_divmod(p, d[i][t], d[t][t])
          if q.length() != 0 {
            for c in 0..<n {
              let qc = up_mul(p, q, d[t][c])
              d[i][c] = up_norm(p, up_add(p, d[i][c], up_neg(p, qc)))
            }
          }
          if d[i][t].length() != 0 {
            let tmp = d[t]
            d[t] = d[i]
            d[i] = tmp
            restart = true
            break
          }
        }
      }
      if restart {
        continue
      }
      // 2b. 行 t 右方清零
      for j in (t + 1)..<n {
        if d[t][j].length() != 0 {
          let (q, _r) = up_divmod(p, d[t][j], d[t][t])
          if q.length() != 0 {
            for r in 0..<m {
              let qt = up_mul(p, q, d[r][t])
              d[r][j] = up_norm(p, up_add(p, d[r][j], up_neg(p, qt)))
            }
          }
          if d[t][j].length() != 0 {
            for r in 0..<m {
              let x = d[r][t]
              d[r][t] = d[r][j]
              d[r][j] = x
            }
            restart = true
            break
          }
        }
      }
      if restart {
        continue
      }
      // 2c. 主元整除子矩陣？
      let mut bi = -1
      let mut bj = -1
      for i in (t + 1)..<m {
        for j in (t + 1)..<n {
          if !up_divides(p, d[t][t], d[i][j]) {
            bi = i
            bj = j
          }
        }
      }
      if bi == -1 {
        ok = true
      } else {
        let (q, _r) = up_divmod(p, d[bi][bj], d[t][t])
        if q.length() != 0 {
          for r in 0..<m {
            let qt = up_mul(p, q, d[r][t])
            d[r][bj] = up_norm(p, up_add(p, d[r][bj], up_neg(p, qt)))
          }
        }
        let tmp = d[t]
        d[t] = d[bi]
        d[bi] = tmp
        for r in 0..<m {
          let x = d[r][t]
          d[r][t] = d[r][bj]
          d[r][bj] = x
        }
      }
    }
    t = t + 1
  }
  // 首一化 + 收集對角
  let diag : Array[Array[Int32]] = []
  let lim_u = if m < n { m } else { n }
  for i in 0..<lim_u {
    diag.push(up_monic(p, d[i][i]))
  }
  diag
}

///==========================================================================
/// 6. GF(2) 布爾函數代數標準形（ANF / Reed–Muller）
///==========================================================================

///|
/// 定義（代數標準形）：布爾函數 `f : {0,1}^n → {0,1}` 有唯一多線性表示
/// `f(x) = ⊕_{S ⊆ [n]} c_S · ∏_{i∈S} x_i`（GF(2) 上，⊕ 為 XOR）。
/// `c_S` 稱 Möbius 系數；`deg f = max{|S| : c_S = 1}`（Re–Muller 碼的次數）。
///
/// 演算法（Möbius / 子集 Zeta 變換，`O(n·2ⁿ)`）：
/// 對每個變數位 i：`c[m] ← c[m] ⊕ c[m ⊖ 2^i]`（m 含位 i）。
/// 真值表以掩碼索引：`table[m] = f(x)`，`x_i =` m 的第 i 位。
///
/// 定理（唯一性 + 反演）：Möbius 變換是 GF(2) 上真值表 ↔ 係數的**對合**
/// （`anf_eval(anf_transform(f)) = f` 往返）；`f ⊕ g` 的係數 = 係數逐位 XOR
/// （線性性）。
/// 定理（經典展開）：多數函數 `maj₃ = x₀x₁ ⊕ x₀x₂ ⊕ x₁x₂`（次數 2）、
/// 奇偶 `⊕x_i`（線性，次數 1）、AND_n `∏x_i`（次數 n）—— 由斷言測試給出。
/// 定理（對合）：Möbius 變換平方 = 恆等（`transform(transform(f)) = f`）。
pub fn anf_transform(n : Int32, table : Array[Int32]) -> Array[Int32] {
  if n < 0 {
    abort("anf_transform: n must be >= 0")
  }
  let size = pow2(n)
  if table.length() != size {
    abort("anf_transform: truth table length must be 2^n")
  }
  let c : Array[Int32] = []
  for m in 0..<size {
    c.push(@num.mod_pos(table[m], 2))
  }
  let mut i = 0
  while i < n {
    let bit = pow2(i)
    for m in 0..<size {
      if @num.mod_pos(m / bit, 2) == 1 {
        c[m] = @num.mod_pos(c[m] + c[m - bit], 2)
      }
    }
    i = i + 1
  }
  c
}

///|
/// 2^n（避免運算子歧義的小工具；n ≥ 0）。
fn pow2(n : Int32) -> Int32 {
  let mut r = 1
  let mut i = 0
  while i < n {
    r = r * 2
    i = i + 1
  }
  r
}

///|
/// ANF 求值：`f(x) = ⊕_{S ⊆ bits(x)} c_S`（掩碼 `x` 下對所有子集掩碼 XOR）。
pub fn anf_eval(n : Int32, coeffs : Array[Int32], x : Int32) -> Int32 {
  let size = pow2(n)
  if coeffs.length() != size {
    abort("anf_eval: coefficient length must be 2^n")
  }
  let mut acc = 0
  for s in 0..<size {
    // s ⊆ x ⟺ s 的每位 1 都在 x 中
    let mut sub = true
    let mut i = 0
    while i < n {
      let bit = pow2(i)
      if @num.mod_pos(s / bit, 2) == 1 && @num.mod_pos(x / bit, 2) != 1 {
        sub = false
      }
      i = i + 1
    }
    if sub {
      acc = @num.mod_pos(acc + coeffs[s], 2)
    }
  }
  acc
}

///|
/// ANF 次數（Reed–Muller 次數）：`max |S|` over `c_S = 1`；零函數回 −1。
pub fn anf_degree(coeffs : Array[Int32]) -> Int32 {
  let mut best = -1
  for m in 0..<coeffs.length() {
    if @num.mod_pos(coeffs[m], 2) == 1 {
      // popcount
      let mut cnt = 0
      let mut v = m
      while v > 0 {
        if @num.mod_pos(v, 2) == 1 {
          cnt = cnt + 1
        }
        v = v / 2
      }
      if cnt > best {
        best = cnt
      }
    }
  }
  best
}
