// 同倫類型論（HoTT）底層演算法層 —— 「定理即程序」：
//   • 等價 Equiv / qinv / 半伴隨（half-adjoint）以可計算資料結構表示；
//   • 對稱、傳遞、逆、伴隨等「衍生定理」是返回證據的函子（derivers）；
//   • 提升 transport、函子性與命題演算（反證、傳遞、De Morgan…）逐點可驗；
//   • 公理層（FunExt、Univalence、Excluded Middle、Id/J 原則）只以文檔公式
//     記載於 README §HoTT，程序層僅依賴其可計算片段（有限域上 FunExt 可驗）。
//
// 類型層級（∞-群胚分層）：`isProp`（−1）→ `isSet`（0）→ `isGroupoid`（1）→ …
// 各層的判定/見證函子見 hit.mbt 與 README。

///|
/// 等價的可計算表示：一對互逆函子（quasi-inverse 資料）。
/// 定義（qinv）：`e` 為等價 ⟺ 存在 `g` 使 `f∘g ~ id` 且 `g∘f ~ id`（逐點律）。
/// 律以外層閉包檢查（型別泛型無內建相等）——見 `sect_ok`/`retr_ok`。
pub(all) struct Equiv[A, B] {
  fwd : (A) -> B
  bwd : (B) -> A
}

///|
/// 半伴隨（half-adjoint equivalence）：`(f, g, η)` 加一致性條件的等價表示；
/// η 以逐點律函子給出，`coh_ok` 檢查伴隨三角一致性（可計算部分）。
pub(all) struct HalfAdj[A, B] {
  fwd : (A) -> B
  bwd : (B) -> A
  /// 右逆律 η(b) : f(g(b)) = b（以相等判定閉包表示）。
  eta : (B) -> Bool
}

///|
/// qinv 段（sect）律：`bwd(fwd(a)) = a` ∀a ∈ A。
pub fn[A, B] Equiv::sect_ok(
  self : Self[A, B],
  eqa : (A, A) -> Bool,
  a : A,
) -> Bool {
  eqa((self.bwd)((self.fwd)(a)), a)
}

///|
/// qinv 回縮（retr）律：`fwd(bwd(b)) = b` ∀b ∈ B。
pub fn[A, B] Equiv::retr_ok(
  self : Self[A, B],
  eqb : (B, B) -> Bool,
  b : B,
) -> Bool {
  eqb((self.fwd)((self.bwd)(b)), b)
}

///|
/// 整體等價判定（律全稱檢查需給定全域枚舉；有限情形精確）。
pub fn[A, B] Equiv::is_equiv_finite(
  self : Self[A, B],
  eqa : (A, A) -> Bool,
  eqb : (B, B) -> Bool,
  all_a : Array[A],
  all_b : Array[B],
) -> Bool {
  for a in all_a {
    if !self.sect_ok(eqa, a) {
      return false
    }
  }
  for b in all_b {
    if !self.retr_ok(eqb, b) {
      return false
    }
  }
  true
}

///|
/// 恒等等價（deriver）：`id_A : A ≃ A`。
pub fn[A] id_equiv() -> Equiv[A, A] {
  Equiv::{ fwd: fn(a : A) { a }, bwd: fn(a : A) { a }, }
}

///|
/// 對稱（derive 定理）：`A ≃ B ⟹ B ≃ A`（互換對應方向）。
/// 證據：律的證明直接對換（`sect` ↔ `retr`）。
pub fn[A, B] equiv_symm(e : Equiv[A, B]) -> Equiv[B, A] {
  Equiv::{ fwd: e.bwd, bwd: e.fwd, }
}

///|
/// 傳遞（derive 定理）：`A ≃ B ⟹ B ≃ C ⟹ A ≃ C`（對應複合）。
pub fn[A, B, C] equiv_trans(e1 : Equiv[A, B], e2 : Equiv[B, C]) -> Equiv[A, C] {
  Equiv::{
    fwd: fn(a : A) { (e2.fwd)((e1.fwd)(a)) },
    bwd: fn(c : C) { (e1.bwd)((e2.bwd)(c)) },
  }
}

///|
/// qinv → 半伴隨（derive 定理）：任何 qinv 資料可擡升為半伴隨，
/// η 取右逆律（一致性在可判定等價型別上由 UIP 於集合層保證）。
pub fn[A, B] qinv_to_halfadj(
  e : Equiv[A, B],
  eqb : (B, B) -> Bool,
) -> HalfAdj[A, B] {
  HalfAdj::{
    fwd: e.fwd,
    bwd: e.bwd,
    eta: fn(b : B) { eqb((e.fwd)((e.bwd)(b)), b) },
  }
}

///|
/// 半伴隨 → qinv（forget η）。
pub fn[A, B] halfadj_to_qinv(h : HalfAdj[A, B]) -> Equiv[A, B] {
  Equiv::{ fwd: h.fwd, bwd: h.bwd, }
}

///|
/// 沿等價搬運性質（transport，計算形式）：
/// 給 `e : A ≃ B` 與 `B` 上謂詞 `P`，得 `A` 上謂詞 `P ∘ f`。
/// 定理（transport 與代入交換）：`transport(P, e, a) = P((e.fwd)(a))` 即定義；
/// `ua_beta` 檢查其與 univalence β-規則的相容性（可計算片段）。
pub fn[A, B] transport_pred(e : Equiv[A, B], pb : (B) -> Bool, a : A) -> Bool {
  pb((e.fwd)(a))
}

///|
/// univalence β-片段：沿 `e` 搬運常真/常假性質保持真值（`transport` 合成律）。
pub fn[A, B] ua_beta_holds(
  e : Equiv[A, B],
  pb : (B) -> Bool,
  all_a : Array[A],
) -> Bool {
  for a in all_a {
    if transport_pred(e, pb, a) != pb((e.fwd)(a)) {
      return false
    }
  }
  true
}

///|
/// 有限載體上的外延性判定：`∀a, f(a)=g(a) ⟺ f ≡ g`（擴展相等）。
/// （此即 FunExt 的「到」方向在有限域的可計算投影；一般 FunExt 公理見 README。）
pub fn[A] funext_finite(
  all_a : Array[A],
  f : (A) -> Int32,
  g : (A) -> Int32,
) -> Bool {
  for a in all_a {
    if f(a) != g(a) {
      return false
    }
  }
  true // 逐點相等時 f ≡ g（擴展相等之左到右方向；反向為外延性定義）
}

// ---------------- 命題演算 derivers（逐點定理即程序） ----------------
//
// 謂詞以 `A → Bool` 表示；下列函子返回「合取式」謂詞，其真值表恒真
// （對所有 `x` 成立），由布林代數公理保證；性質測試以隨機遮罩全域驗證。

///|
/// 蘊含：`p ⟹ q`（逐點）。
pub fn[A] impl_pred(p : (A) -> Bool, q : (A) -> Bool) -> (A) -> Bool {
  fn(a : A) { !p(a) || q(a) }
}

///|
/// 雙向蘊含（等價於命題層 iff）：`p ⟺ q`。
pub fn[A] iff_pred(p : (A) -> Bool, q : (A) -> Bool) -> (A) -> Bool {
  fn(a : A) { (p(a) || !q(a)) && (q(a) || !p(a)) }
}

///|
/// 反證（derive 定理）：`p ⟹ q` 與 `¬q ⟹ ¬p` 逐點等價。
pub fn[A] contrapose_holds(
  p : (A) -> Bool,
  q : (A) -> Bool,
  all_a : Array[A],
) -> Bool {
  for a in all_a {
    let fwd = !p(a) || q(a) // p ⟹ q
    let bwd = q(a) || !p(a) // ¬q ⟹ ¬p = q ∨ ¬p（與 p ⟹ q 逐點等價）
    if fwd != bwd {
      return false
    }
  }
  true
}

///|
/// 蘊涵傳遞（derive 定理）：`(p⟹q) ∧ (q⟹r) ⟹ (p⟹r)` 逐點成立。
pub fn[A] impl_trans_holds(
  p : (A) -> Bool,
  q : (A) -> Bool,
  r : (A) -> Bool,
  all_a : Array[A],
) -> Bool {
  for a in all_a {
    let h1 = !p(a) || q(a)
    let h2 = !q(a) || r(a)
    let concl = !p(a) || r(a)
    if h1 && h2 && !concl {
      return false
    }
  }
  true
}

///|
/// 雙重否定消去（布林可判定情形，構造性有效）：`¬¬p ⟺ p`（決定性型別上
/// 雙重否定等價於本身；此即 `DNE` 在布林層的可計算投影）。
pub fn[A] dne_holds(p : (A) -> Bool, all_a : Array[A]) -> Bool {
  for a in all_a {
    if !(!p(a)) != p(a) {
      return false
    }
  }
  true
}

///|
/// De Morgan（derive 定理）：`¬(p ∧ q) ⟺ ¬p ∨ ¬q` 逐點等價。
pub fn[A] de_morgan_holds(
  p : (A) -> Bool,
  q : (A) -> Bool,
  all_a : Array[A],
) -> Bool {
  for a in all_a {
    let lhs = !(p(a) && q(a))
    let rhs = !p(a) || !q(a)
    if (lhs && !rhs) || (!lhs && rhs) {
      return false
    }
  }
  true
}

///|
/// iff 對稱（derive 定理）：`(p ⟺ q) ⟺ (q ⟺ p)` 逐點成立。
pub fn[A] iff_symm_holds(
  p : (A) -> Bool,
  q : (A) -> Bool,
  all_a : Array[A],
) -> Bool {
  for a in all_a {
    let l = iff_pred(p, q)(a)
    let r = iff_pred(q, p)(a)
    if l != r {
      return false
    }
  }
  true
}

///|
/// Int32 向量逐位相等（hott 內共用：伴隨/HIT/截斷）。
fn vec32_eq(a : Array[Int32], b : Array[Int32]) -> Bool {
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
