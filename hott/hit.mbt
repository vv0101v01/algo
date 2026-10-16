// 高階歸納類型（HIT）與截斷層級 —— 計算模型：
//   • S¹：單一構造子 `base` 加路徑 `loop`；路徑空間以繞數 `ℤ` 表示，
//     得 π₁(S¹) ≅ ℤ 的等價證據（encode/decode 論證的計算核心）；
//   • 集合商（quotient HIT）：構造子 `cls : R → Q`、路徑公理 `cls a = cls b ⟺ a−b ∈ I`，
//     消去定理以 well-definedness 檢查器呈現；
//   • 截斷層級：`isProp`（−1）判定器、`S¹` 非集合見證（1-型）、UIP 見證。
// 無窮層塔：`Contr ⊂ Prop ⊂ Set ⊂ Groupoid ⊂ …`（README 公式）。

///|
/// S¹ 的基本群元素 = 繞數（HIT 路徑 `loop^n : base = base` 的計算表示）。
/// 構造子層：`s1_base` 唯一；路徑層由 `loop` 生成（覆蓋空間 `ℝ → S¹` 之 `e ↦ (x mod 1)`）。
pub fn s1_loop(n : Int32) -> Int32 {
  n
}

///|
/// 路徑合成（π₁ 群運算）：繞數相加。
/// 定理（群公理）：`(ℤ, +, 0, −)` 為阿貝爾群 — 結合律/單位元/逆元逐點成立（見測試）。
pub fn s1_concat(p : Int32, q : Int32) -> Int32 {
  p + q
}

///|
/// 路徑逆（反向路徑）：繞數取負。
pub fn s1_inv(p : Int32) -> Int32 {
  -p
}

///|
/// 恒等路徑（ reflexivity ）。
pub fn s1_refl() -> Int32 {
  0
}

///|
/// π₁(S¹) ≅ ℤ 的等價資料（定理即程序）：
/// `fwd = loop`（整數 → 路徑）、`bwd = 繞數`（路徑 → 整數）；
/// encode∘decode = id 且 decode∘encode = id 於路徑模型內逐點成立。
/// 這正是「S¹ 覆蓋空間論證」的計算內核：`p : loop^n ↦ n` 為雙射。
pub fn pi1_s1_equiv() -> Equiv[Int32, Int32] {
  Equiv::{ fwd: s1_loop, bwd: fn(p : Int32) { p }, }
}

///|
/// S¹ 萊布尼茲/函子性：路徑複合與逆的群律檢查（恆真於整數模型）。
pub fn s1_groupoid_laws(p : Int32, q : Int32, r : Int32) -> Bool {
  s1_concat(s1_concat(p, q), r) == s1_concat(p, s1_concat(q, r)) &&
  s1_concat(p, s1_refl()) == p &&
  s1_concat(s1_refl(), p) == p &&
  s1_concat(p, s1_inv(p)) == s1_refl() &&
  s1_concat(s1_inv(p), p) == s1_refl()
}

///|
/// 集合商 HIT 的路徑判定：`cls(a) = cls(b) ⟺ a − b ∈ I`。
///（以有限代數的陪集成員判定計算。）
pub fn quotient_path(
  alg : @finite.FinAlg,
  i : @finite.FinIdeal,
  a : Array[Int32],
  b : Array[Int32],
) -> Bool {
  let diff = alg.add_elem(a, alg.neg_elem(b))
  i.contains(diff)
}

///|
/// 商 HIT 消去定理（well-definedness 檢查器）：
/// `f : R → S` 可經商誘導 `f̄ : Q → S` ⟺ `f` 在 I-陪集上常值
/// （即 `a − b ∈ I ⟹ f(a) = f(b)`）。此即 HIT 消去法則
/// `rec_Q(f) ∘ cls = f` 的可判定投影；無窮掃描於有限環精確。
pub fn quotient_rec_ok(
  alg : @finite.FinAlg,
  i : @finite.FinIdeal,
  f : (Array[Int32]) -> Int32,
) -> Bool {
  for x in alg.all_elements() {
    for d in i.members {
      let y = alg.add_elem(x, d)
      if f(x) != f(y) {
        return false
      }
    }
  }
  true
}

///|
/// `isProp` 判定（−1 截斷）：載體中任意兩元素相等（可判定相等下精確）。
/// 定理：`isProp A` ⟺ `A` 至多一個元素；`Contr A ≃ isProp A ∧ ‖A‖`（README）。
pub fn is_prop_elems(elems : Array[Array[Int32]]) -> Bool {
  if elems.length() == 0 {
    return true // 空類型 vacuously prop（依慣例；some 定義要求 inhabited）
  }
  let first = elems[0]
  for x in elems {
    if !vec32_eq(first, x) {
      return false
    }
  }
  true
}

///|

///|
/// `S¹` 非集合（isSet 失敗）的見證：路徑 `loop⁰ ≠ loop¹`（繞數不同），
/// 但「路徑之間的道路」由繞數相等決定（UIP於路徑層）——故 `S¹` 是 1-型而非 0-型。
/// 算法即見證：返回 `false` 表示「S¹ 的路徑空間是集合」不成立。
pub fn s1_is_set() -> Bool {
  // isSet S¹ 要求所有平行路徑相等；以 loop⁰ vs loop¹ 逐點檢查（恒 false ⇒ 非集合）
  s1_loop(0) == s1_loop(1)
}

///|
/// UIP/K 於整數模型（0-層）：任意兩條相等的道路同構 —— 模型中道路即整數，
/// 「a = b」的證據唯一 ⇔ 判等為真時唯一（`int_refl_unique` 恆真）。
pub fn int_refl_unique(a : Int32) -> Bool {
  a == a
}
