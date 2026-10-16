// 上輪遺漏的結構層演算法：單純理想、半單性（Wedderburn–Artin）、芯（socle）。

///|
/// 是否為域（有限交換含幺代數的判定算法）：無零因子（既約）且每個非零元可逆
/// （窮舉乘法表，`p^dim` 小時為精確判定）。
/// 定理（Wedderburn 小定理的有限形式）：有限整環 ⟺ 有限域。
pub fn is_field_alg(alg : FinAlg) -> Bool {
  if alg.dim == 0 {
    return false // 零環：1 = 0，非域
  }
  let elems = alg.all_elements()
  let one = alg.one_elem()
  let zero = alg.zero_elem()
  for x in elems {
    if @linalg.vec_eq(x, zero) {
      continue
    }
    let mut invertible = false
    for y in elems {
      if @linalg.vec_eq(alg.mul_elem(x, y), one) {
        invertible = true
      }
    }
    if !invertible {
      return false
    }
  }
  true
}

///|
/// 單純理想（定義）：非零理想 `I` 且理想格中 `{0} ⊊ J ⊊ I` 不存在。
/// 定理：交換 Artin 環的單純理想為理想格中的極小非零元；有限交換環中
/// 單純理想作為模同構於 `𝔽_p`。
pub fn is_simple_ideal(i : FinIdeal) -> Bool {
  if i.members.length() <= 1 {
    return false // 零理想（單元素 [0]）非單純
  }
  for j in enumerate_ideals(i.alg) {
    if j.members.length() <= 1 {
      continue // 跳過零理想（唯一允許的更小理想）
    }
    if j.members.length() < i.members.length() && ideal_subset(j, i) {
      return false
    }
  }
  true
}

///|
/// 全部單純理想（算法）：過濾理想格取極小非零元。
pub fn simple_ideals(alg : FinAlg) -> Array[FinIdeal] {
  let all = enumerate_ideals(alg)
  let out : Array[FinIdeal] = []
  for i in all {
    if i.members.length() <= 1 {
      continue // 跳過零理想
    }
    let mut minimal = true
    for j in all {
      if j.members.length() <= 1 {
        continue // 跳過零理想
      }
      if j.members.length() < i.members.length() && ideal_subset(j, i) {
        minimal = false
      }
    }
    if minimal {
      out.push(i)
    }
  }
  out
}

///|
/// 理想包含判定：`J ⊆ I`（所有 `J` 成員屬 `I`）。
fn ideal_subset(j : FinIdeal, i : FinIdeal) -> Bool {
  for x in j.members {
    if !i.contains(x) {
      return false
    }
  }
  true
}

///|
/// 芯（socle，定義）：`soc(R) = Ann(J(R))` — 被 Jacobson 根零化的一切元素；
/// 交換 Artin 環中 `soc(R)` ≅ 直積各域分量的 `𝔽_p`（單純模直和）。
/// 定理：`soc ≠ 0` ⟺ 環有單純直和項；`soc` 本身是半單模。
pub fn socle(alg : FinAlg) -> FinIdeal {
  annihilator_ideal(jacobson_radical(alg))
}

///|
/// 半單環判定（交換 Artin 情形）：`J(R) = 0`。
/// 定理（Wedderburn–Artin，交換形式）：下列等價 —
/// (1) `J(R) = 0`；(2) `R` 是域的有限直積；(3) `R` 作為模半單；
/// (4) 每個模投射（= 既約直和項結構）。見 `wedderburn_fields` 與性質測試。
pub fn is_semisimple_ring(alg : FinAlg) -> Bool {
  jacobson_radical(alg).eq(alg.zero_ideal()) // J = {0}（規範表示：單元素 [0]）
}

///|
/// Wedderburn 直積分解（算法）：`R ≅ ∏ F_i` 的各域角（primitive idempotent 角）。
/// 定理：交換 Artin 半單 ⟺ 全部角為域且 `Σ dim F_i = dim R`。
pub fn wedderburn_fields(alg : FinAlg) -> Array[FinAlg] {
  let out : Array[FinAlg] = []
  let prims = primitive_idempotents(alg)
  if prims.length() == 0 {
    // 無非平凡冪等元 ⇒ 單塊：R 自身（冪等元僅 {0,1} 且 R ≠ 0 時；
    // R 為域時此塊即該域；局部 Artinan 情形由 is_field_alg 決定真假）
    if alg.dim >= 1 && idempotents(alg).length() == 2 {
      out.push(alg)
    }
    return out
  }
  for e in prims {
    out.push(corner(alg, e))
  }
  out
}

///|
/// Wedderburn–Artin 驗證（定理即程序）：半單且每角為域且維數直和匹配。
pub fn is_wedderburn_product(alg : FinAlg) -> Bool {
  if !is_semisimple_ring(alg) {
    return false
  }
  let fs = wedderburn_fields(alg)
  let mut total = 0
  for f in fs {
    if !is_field_alg(f) {
      return false
    }
    total = total + f.dim
  }
  total == alg.dim
}
