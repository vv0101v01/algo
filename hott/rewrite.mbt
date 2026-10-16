// 既有定理的 HoTT 重寫層：把代數定理重寫為等價（Equiv）與搬運（transport）證據。
//   • 中國剩餘定理 ℤ/n ≅ ∏ ℤ/p^k（fwd = 取剩餘、bwd = 合併）——等價即定理；
//   • 零化子加法律 Ann(I+J) = Ann(I) ∩ Ann(J)——判定即證據（性質測試隨機驗證）。

///|
/// CRT 前向：`x ↦ (x mod m_i)_i`。
pub fn crt_forward(mods : Array[Int32], x : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for m in mods {
    out.push(@num.mod_pos(x, m))
  }
  out
}

///|
/// CRT 逆向（逐對合併，要求模兩兩互素）：剩餘組 → `[0, Πm_i)` 的唯一代表。
/// 定理（CRT 存在唯一性）：模互素時合併結果與次序無關、且
/// `recombine(forward(x)) = x (mod n)`；此程序給出顯式構造。
pub fn crt_recombine(mods : Array[Int32], residues : Array[Int32]) -> Int32 {
  if mods.length() != residues.length() {
    abort("crt_recombine: length mismatch")
  }
  if mods.length() == 0 {
    return 0
  }
  let mut acc = @num.mod_pos(residues[0], mods[0])
  let mut big = mods[0]
  let mut i = 1
  while i < mods.length() {
    let mi = mods[i]
    let ri = @num.mod_pos(residues[i], mi)
    // 解 big·t ≡ ri − acc (mod mi)
    let diff = @num.mod_pos(ri - @num.mod_pos(acc, mi), mi)
    let bmod = @num.mod_pos(big, mi)
    match @num.invmod(bmod, mi) {
      Some(t0) => {
        let t = @num.mod_pos(diff * t0, mi)
        acc = acc + big * t
        big = big * mi
        acc = @num.mod_pos(acc, big)
      }
      None => abort("crt_recombine: moduli not coprime")
    }
    i = i + 1
  }
  acc
}

///|
/// CRT 等價律檢查（定理即程序，有限全域精確）：
/// 對 `n ≥ 1` 的素冪分解模組，`∀x ∈ [0,n): recombine(forward(x)) = x`，
/// 且 `forward` 於 `[0,n)` 單射（roundtrip 雙向）——即 `ℤ/n ≃ ∏ ℤ/p^k` 的證據。
pub fn crt_equiv_holds(n : Int32) -> Bool {
  if n <= 1 {
    return true
  }
  if n > 4096 {
    abort("crt_equiv_holds: n too large (cap 4096)")
  }
  let mods = @poly.zn_crt_components(n)
  for x in 0..<n {
    let r = crt_forward(mods, x)
    if crt_recombine(mods, r) != x {
      return false
    }
  }
  // 單射（不同 x 不同剩餘組）：由 roundtrip 已蘊涵，再驗一組邊界
  let mut seen_first = -1
  if mods.length() > 0 {
    seen_first = crt_forward(mods, 0)[0]
    if seen_first != 0 {
      return false
    }
  }
  true
}

///|
/// 零化子加法律（derive 定理）：`Ann(I + J) = Ann(I) ∩ Ann(J)`。
/// 判定即證據：兩理想逐元素比較；性質測試以隨機生成理想全域驗證。
pub fn ann_sum_law(i : @finite.FinIdeal, j : @finite.FinIdeal) -> Bool {
  let lhs = @finite.annihilator_ideal(i.add(j))
  let rhs = @finite.annihilator_ideal(i).intersect(@finite.annihilator_ideal(j))
  lhs.eq(rhs)
}
