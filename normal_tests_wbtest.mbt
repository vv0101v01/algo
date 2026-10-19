// Whitebox tests for `normal.mbt`（規範形式）：斷言 + 性質（憑證式）。

///|
/// 确定性偽隨機：LCG on ℤ/M，`M = 2^31 − 1`（`@num.mul_mod` 無溢出）。
/// （本檔屬 root 包：root **不可**匯入 `testutil` —— `testutil → finite → root`
///   會構成依賴環；故此測試專用 PRNG 就地定義，`cat` 包則經 testutil 共用。）
fn trand(seed : Int32, salt : Int32, m : Int32) -> Int32 {
  let mm = 2147483647
  let base = @num.mod_pos(seed, mm)
  let x = @num.mod_pos(
    @num.mul_mod(base, 1103515245, mm) + @num.mul_mod(salt, 1234579, mm),
    mm,
  )
  @num.mod_pos(x, m)
}

///|
/// ℤ 矩陣乘法（憑證計算用；小矩陣）。
fn imul(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let m = a.length()
  let k = b.length()
  let n = if k == 0 { 0 } else { b[0].length() }
  let out : Array[Array[Int32]] = []
  for i in 0..<m {
    let row : Array[Int32] = []
    for j in 0..<n {
      let mut acc = 0
      for t in 0..<k {
        acc = acc + a[i][t] * b[t][j]
      }
      row.push(acc)
    }
    out.push(row)
  }
  out
}

///|
/// 二維整數數組相等。
fn rows_eq(a : Array[Array[Int32]], b : Array[Array[Int32]]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if a[i].length() != b[i].length() {
      return false
    }
    for j in 0..<a[i].length() {
      if a[i][j] != b[i][j] {
        return false
      }
    }
  }
  true
}

///|
/// 全零矩陣判定。
fn rows_all_zero(a : Array[Array[Int32]]) -> Bool {
  for r in a {
    for x in r {
      if x != 0 {
        return false
      }
    }
  }
  true
}

///|
/// 𝔽_p 上矩陣冪的跡 `tr(A^k)`（相似不變量檢驗用）。
fn trace_of_pow(p : Int32, a : Array[Array[Int32]], k : Int32) -> Int32 {
  let n = a.length()
  let mut acc = @linalg.Matrix::identity(p, n)
  let m = @linalg.Matrix::from_rows(p, a)
  let mut i = 0
  while i < k {
    acc = acc.mul(m)
    i = i + 1
  }
  let mut tr = 0
  for r in 0..<n {
    tr = @num.mod_pos(tr + acc.data[r][r], p)
  }
  tr
}

///|
/// 行列式：已知值 + 多線性（det(A·B) = det A · det B）性質。
test "det_gf: known values, multiplicativity, singularity" {
  // [[1,2],[3,4]]：det = 4 − 6 = −2 ≡ 5 (mod 7)
  let a = @linalg.Matrix::from_rows(7, [[1, 2], [3, 4]])
  assert_eq(det_gf(a), 5)
  // 單位陣 det = 1
  assert_eq(det_gf(@linalg.Matrix::identity(11, 3)), 1)
  // 奇異（行成比例）det = 0
  let s = @linalg.Matrix::from_rows(5, [[1, 2, 3], [2, 4, 6], [0, 1, 1]])
  assert_eq(det_gf(s), 0)
  // 性質：det(A·B) ≡ det A · det B (mod p)
  @quickcheck.check((seed : Int32) => {
    let p = 7
    let n = 3
    let ra : Array[Array[Int32]] = []
    let rb : Array[Array[Int32]] = []
    for i in 0..<n {
      let rowa : Array[Int32] = []
      let rowb : Array[Int32] = []
      for j in 0..<n {
        rowa.push(trand(seed, i * 31 + j * 7 + 1, p))
        rowb.push(trand(seed + 977, i * 13 + j * 3 + 2, p))
      }
      ra.push(rowa)
      rb.push(rowb)
    }
    let ma = @linalg.Matrix::from_rows(p, ra)
    let mb = @linalg.Matrix::from_rows(p, rb)
    let prod = ma.mul(mb)
    @num.mul_mod(det_gf(ma), det_gf(mb), p) == det_gf(prod)
  })
}

///|
/// 特徵多項式：已知伴隨矩陣、Cayley–Hamilton、χ(x) = det(xI − A)、
/// 跡/行列式係數一致性。
test "mat_charpoly: companion known case, Cayley-Hamilton, coefficient theorems" {
  // A = [[0,4],[1,0]] over 𝔽₅ = companion(t² + 1)：χ = t² + 1 → [1, 0, 1]
  let a = @linalg.Matrix::from_rows(5, [[0, 4], [1, 0]])
  let chi = mat_charpoly(a)
  assert_eq(chi, [1, 0, 1])
  // χ(A) = 0（Cayley–Hamilton）
  let ca = mat_poly_eval(chi, a)
  assert_true(rows_all_zero(ca.data))
  // tr A = −a_{n−1}、det A = (−1)^n a_0
  let tr = @num.mod_pos(a.data[0][0] + a.data[1][1], 5)
  assert_eq(tr, @num.mod_pos(-chi[1], 5))
  assert_eq(det_gf(a), @num.mod_pos(chi[0], 5)) // (−1)²·a₀ = a₀（n = 2 偶）
  // χ(x) = det(xI − A) 對多個 x（插值一致性）
  for x in 0..<5 {
    assert_eq(
      up_eval(5, chi, x),
      det_gf(
        @linalg.Matrix::from_rows(5, [
          [x - a.data[0][0], -a.data[0][1]],
          [-a.data[1][0], x - a.data[1][1]],
        ]),
      ),
    )
  }
  // 性質：隨機矩陣的 Cayley–Hamilton
  @quickcheck.check((seed : Int32) => {
    let p = 5
    let n = 3
    let rows : Array[Array[Int32]] = []
    for i in 0..<n {
      let row : Array[Int32] = []
      for j in 0..<n {
        row.push(trand(seed + 31, i * 17 + j * 5 + 3, p))
      }
      rows.push(row)
    }
    let m = @linalg.Matrix::from_rows(p, rows)
    let cp = mat_charpoly(m)
    // 首一 + 次數 n
    assert_eq(cp.length(), n + 1)
    assert_eq(cp[n], 1)
    // Cayley–Hamilton
    let ev = mat_poly_eval(cp, m)
    rows_all_zero(ev.data) &&
    ({
      // 跡 = −a_{n−1}
      let trm = @num.mod_pos(m.data[0][0] + m.data[1][1] + m.data[2][2], p)
      trm == @num.mod_pos(-cp[n - 1], p)
    })
  })
}

///|
/// Smith 規範形式：經典例子 + 憑證（U·A·V = D、det U/V = ±1、整除鏈）。
test "snf_int: certificates U·A·V=D, det=±1, divisibility chain" {
  // 經典：[[2,4],[6,8]] → diag(2, 4)
  let a = [[2, 4], [6, 8]]
  let (d, u, v) = snf_int(a)
  assert_eq(d, [2, 4])
  // 憑證 1：U·A·V = D
  assert_true(rows_eq(imul(imul(u, a), v), [[d[0], 0], [0, d[1]]]))
  // 憑證 2：det U = ±1、det V = ±1
  assert_true(det_int(u) == 1 || det_int(u) == -1)
  assert_true(det_int(v) == 1 || det_int(v) == -1)
  // 單位陣 → 全 1 對角；零陣 → 全 0
  let (d1, _, _) = snf_int([[1, 0, 0], [0, 1, 0], [0, 0, 1]])
  assert_eq(d1, [1, 1, 1])
  let (d0, _, _) = snf_int([[0, 0], [0, 0]])
  assert_eq(d0, [0, 0])
  // 性質：隨機小矩陣的全部憑證
  @quickcheck.check((seed : Int32) => {
    let n = 2 + trand(seed, 91, 2) // 2..3
    let a2 : Array[Array[Int32]] = []
    for i in 0..<n {
      let row : Array[Int32] = []
      for j in 0..<n {
        row.push(trand(seed + 5, i * 23 + j * 11 + 7, 19) - 9)
      }
      a2.push(row)
    }
    let (dg, u2, v2) = snf_int(a2)
    // 憑證：U·A·V = 對角
    let dmat : Array[Array[Int32]] = []
    for i in 0..<n {
      let row : Array[Int32] = []
      for j in 0..<n {
        row.push(if i == j { dg[i] } else { 0 })
      }
      dmat.push(row)
    }
    let cert = rows_eq(imul(imul(u2, a2), v2), dmat)
    // 幺模
    let uni = det_int(u2) == 1 || det_int(u2) == -1
    let univ = det_int(v2) == 1 || det_int(v2) == -1
    // 整除鏈（0 只能出現在尾部）
    let mut chain = true
    for i in 0..<(n - 1) {
      if dg[i] < 0 {
        chain = false
      }
      if dg[i] != 0 && dg[i + 1] % dg[i] != 0 {
        chain = false
      }
    }
    cert && uni && univ && chain
  })
}

///|
/// Hermite 規範形式：憑證（T·A = H、det T = ±1）+ 結構 + 冪等。
test "hnf_int: lattice certificate, echelon structure, idempotence" {
  // 經典：[[2,4],[6,8]] → [[2,0],[0,4]]（行格 same lattice）
  let a = [[2, 4], [6, 8]]
  let (h, t) = hnf_int(a)
  assert_true(rows_eq(h, [[2, 0], [0, 4]]))
  assert_true(rows_eq(imul(t, a), h))
  let dt = det_int(t)
  assert_true(dt == 1 || dt == -1)
  // 幂等：HNF(HNF(A)) = HNF(A)
  let (h2, _) = hnf_int(h)
  assert_true(rows_eq(h2, h))
  // 性質：隨機小矩陣
  @quickcheck.check((seed : Int32) => {
    let rows_n = 2 + trand(seed, 41, 2) // 2..3 行
    let cols_n = 2 + trand(seed + 3, 43, 2) // 2..3 列
    let a2 : Array[Array[Int32]] = []
    for i in 0..<rows_n {
      let row : Array[Int32] = []
      for j in 0..<cols_n {
        row.push(trand(seed + 11, i * 19 + j * 29 + 5, 21) - 10)
      }
      a2.push(row)
    }
    let (h3, t3) = hnf_int(a2)
    // 憑證 1：T·A = H
    let cert = rows_eq(imul(t3, a2), h3)
    // 憑證 2：det T = ±1
    let dt3 = det_int(t3)
    let uni = dt3 == 1 || dt3 == -1
    // 結構：行 echelon（每行首非零左側全零）+ 正主元 + 上方 ∈ [0, pivot)
    let mut struct_ok = true
    let mut last_piv = -1
    for i in 0..<rows_n {
      // 首個非零列 = 主元列
      let mut first = -1
      for j in 0..<cols_n {
        if first == -1 && h3[i][j] != 0 {
          first = j
        }
      }
      if first == -1 {
        continue // 全零行：只允許出現在尾部（下方統一驗證）
      }
      for j in 0..<first {
        if h3[i][j] != 0 {
          struct_ok = false
        }
      }
      if h3[i][first] <= 0 {
        struct_ok = false
      }
      // 上方取模：pivot 列中所有 i' < i 滿足 0 ≤ h[i'][first] < pivot
      for ip in 0..<i {
        let e = h3[ip][first]
        if e < 0 || e >= h3[i][first] {
          struct_ok = false
        }
      }
      // 主元列指標嚴格遞增
      if first <= last_piv {
        struct_ok = false
      }
      last_piv = first
    }
    // 尾部全零：遇全零行後不得再有非零行
    let mut seen_zero = false
    for i in 0..<rows_n {
      let mut nz = false
      for j in 0..<cols_n {
        if h3[i][j] != 0 {
          nz = true
        }
      }
      if !nz {
        seen_zero = true
      } else if seen_zero {
        struct_ok = false
      }
    }
    // 冪等
    let (h4, _) = hnf_int(h3)
    let idem = rows_eq(h4, h3)
    cert && uni && struct_ok && idem
  })
}

///|
/// 有理標準形：伴隨矩陣 χ 定理、不變因子整除鏈與積、相似不變量
/// `tr(A^k)`、伴隨矩陣的 RCF 冪等。
test "rational_canonical_form: companion charpoly, invariants, trace similarity" {
  // companion(t² + 1) over 𝔽₅ 的 χ 就是自身
  let c = companion_matrix(5, [1, 0, 1])
  let chi_c = mat_charpoly(@linalg.Matrix::from_rows(5, c))
  assert_eq(chi_c, [1, 0, 1])
  // A 為伴隨矩陣 → RCF(A) = A、不變因子 = (1, f)
  let (fac, rcf) = rational_canonical_form(@linalg.Matrix::from_rows(5, c))
  assert_eq(fac.length(), 2)
  assert_eq(fac[0], [1]) // 常數因子
  assert_eq(fac[1], [1, 0, 1])
  assert_true(rows_eq(rcf.data, c))
  // 性質：隨機矩陣
  @quickcheck.check((seed : Int32) => {
    let p = 5
    let n = 2 + trand(seed, 71, 2) // 2..3
    let rows : Array[Array[Int32]] = []
    for i in 0..<n {
      let row : Array[Int32] = []
      for j in 0..<n {
        row.push(trand(seed + 13, i * 37 + j * 17 + 9, p))
      }
      rows.push(row)
    }
    let m = @linalg.Matrix::from_rows(p, rows)
    let (factors, r) = rational_canonical_form(m)
    // (a) 不變因子整除鏈（常數在前）
    let mut chain = true
    let mut prev : Array[Int32] = [1]
    for s in factors {
      // s₁ | s₂：s_prev | s_curr（前一因子必為首一；[1] 整除一切）
      if !up_divides(p, prev, s) {
        chain = false
      }
      prev = s
    }
    // (b) ∏ s_i = χ_A（升冪乘積）
    let mut prod : Array[Int32] = [1]
    for s in factors {
      prod = up_mul(p, prod, s)
    }
    let chi = mat_charpoly(m)
    let prod_ok = rows_eq([prod], [chi])
    // (c) ∑ deg s_i = n（RCF 尺寸，rational_canonical_form 內部已斷言；
    //     這裡獨立驗證）
    let mut total_deg = 0
    for s in factors {
      total_deg = total_deg + s.length() - 1
    }
    // (d) 相似不變量：tr(A^k) = tr(RCF^k)，k = 1..n
    let mut trace_ok = true
    for k in 1..<(n + 1) {
      if trace_of_pow(p, rows, k) != trace_of_pow(p, r.data, k) {
        trace_ok = false
      }
    }
    // (e) RCF 滿足 Cayley–Hamilton
    let ch_r = mat_poly_eval(chi, r)
    let ch_ok = rows_all_zero(ch_r.data)
    chain && prod_ok && total_deg == n && trace_ok && ch_ok
  })
}

///|
/// ANF：經典函數（奇偶、AND、多數）+ 次數定理。
test "anf_transform: parity, AND, majority, Reed-Muller degree" {
  // 奇偶 f = x₀⊕x₁⊕x₂：ANF 就是線性多項式 x₀+x₁+x₂（係數在掩碼 1,2,4）
  let par = [0, 1, 1, 0, 1, 0, 0, 1] // 真值表：popcount 奇 → 1
  let pc = anf_transform(3, par)
  assert_eq(pc, [0, 1, 1, 0, 1, 0, 0, 0])
  assert_eq(anf_degree(pc), 1) // 線性函數 → 次數 1（次數 n 的是 AND_n）
  // 往返：ANF 求值 = 真值表
  for x in 0..<8 {
    assert_eq(anf_eval(3, pc, x), par[x])
  }
  // AND₂：ANF = x₀x₁（掩碼 3）
  assert_eq(anf_transform(2, [0, 0, 0, 1]), [0, 0, 0, 1])
  assert_eq(anf_degree([0, 0, 0, 1]), 2)
  // 零函數：次數 −1
  assert_eq(anf_degree([0, 0, 0, 0]), -1)
  // 多數函數 maj₃ = x₀x₁ ⊕ x₀x₂ ⊕ x₁x₂（GF(2) 恆等式）
  let maj : Array[Int32] = []
  for x in 0..<8 {
    let b0 = @num.mod_pos(x, 2)
    let b1 = @num.mod_pos(x / 2, 2)
    let b2 = @num.mod_pos(x / 4, 2)
    let s = b0 + b1 + b2
    maj.push(if s >= 2 { 1 } else { 0 })
  }
  let majc = anf_transform(3, maj)
  // 期望：掩碼 3,5,6 為 1（x₀x₁, x₀x₂, x₁x₂），其餘 0
  assert_eq(majc, [0, 0, 0, 1, 0, 1, 1, 0])
  assert_eq(anf_degree(majc), 2)
  // 逐點：ANF 求值 == 真值表
  for x in 0..<8 {
    assert_eq(anf_eval(3, majc, x), maj[x])
  }
}

///|
/// ANF：往返反演定理（Möbius 對合）+ 線性性。
test "anf: roundtrip inversion and linearity (properties)" {
  // 性質 1：anf_eval(anf_transform(t), x) = t[x]（唯一性/反演）
  @quickcheck.check((seed : Int32) => {
    let n = 3
    let table : Array[Int32] = []
    for x in 0..<8 {
      table.push(trand(seed + 17, x * 13 + 1, 2))
    }
    let c = anf_transform(n, table)
    let mut all = true
    for x in 0..<8 {
      if anf_eval(n, c, x) != table[x] {
        all = false
      }
    }
    // 對合（Möbius 反演）：變換² = 原真值表
    let c2 = anf_transform(n, c)
    let mut idem = true
    for m in 0..<8 {
      if c2[m] != table[m] {
        idem = false
      }
    }
    all && idem
  })
  // 性質 2：ANF(f ⊕ g) = ANF(f) ⊕ ANF(g)（GF(2) 線性性）
  @quickcheck.check((seed : Int32) => {
    let n = 3
    let t1 : Array[Int32] = []
    let t2 : Array[Int32] = []
    for x in 0..<8 {
      t1.push(trand(seed + 3, x * 7 + 2, 2))
      t2.push(trand(seed + 101, x * 11 + 4, 2))
    }
    let t12 : Array[Int32] = []
    for x in 0..<8 {
      t12.push(@num.mod_pos(t1[x] + t2[x], 2))
    }
    let c1 = anf_transform(n, t1)
    let c2 = anf_transform(n, t2)
    let c12 = anf_transform(n, t12)
    let mut ok = true
    for m in 0..<8 {
      if c12[m] != @num.mod_pos(c1[m] + c2[m], 2) {
        ok = false
      }
    }
    ok
  })
}
