///|
/// 驗證層（verify）：程序端可執行碼 + 合約（contracts）。
///
/// 形式化證明：`moon prove` 生成 V.C.，Why3 + Z3 消解。
/// 設計原則（實測結論）：
///   - 定理 = 函數合約（proof_require / proof_ensure / proof_decrease），
///     定義點的 V.C. 看得見自己的函數體 —— 這是唯一可靠的證明來源；
///   - 後定義的函數可直接引用先前函數的合約作為假設；
///   - #proof_pure 函數在 V.C. 中是抽象符號（無函數體），故不用它承載定理。
///
/// 定理：
///   T1. mod_pos     —— 0 ≤ mod_pos(a, p) < p（p ≠ 0）
///   T2. euclid_divmod —— 帶餘除法 a = q·p + r、0 ≤ r < p
///   T3. pow2_rec    —— 2^n ≥ 1（遞歸終止：proof_decrease n）
///   T4. pow_mod     —— 快速冪結果 ∈ [0, p)（遞歸終止：proof_decrease exp）

///|
/// 定理 T1：取模值域（前置：p > 0；後置：結果 ∈ [0, p)）。
pub fn mod_pos(
  a : Int32,
  p : Int32,
) -> Int32 where {
  proof_require: p > 0,
  proof_ensure: result => {
    in_range(result, p) && (a - result) / p * p + result == a
  },
} {
  // floor(a/p) via trunc-division: trunc = floor for a ≥ 0；a < 0 時
  // (a − p + 1) / p 的被除數為負，trunc = ceil，故正好是 floor。
  let q0 = if a >= 0 { a / p } else { (a - p + 1) / p }
  a - p * q0 // 同餘：a − result = p·q0（乘積形態，讓 Div_exact 直接命中）
}

///|
/// 歐幾里得除法的結果對：商 q 與非負餘 r。
pub struct Euclid {
  q : Int32
  r : Int32
}

///|
/// 定理 T2（帶餘除法 / division algorithm）：
/// 對 p > 0，回傳的 (q, r) 滿足 a = q·p + r 且 0 ≤ r < p。
pub fn euclid_divmod(
  a : Int32,
  p : Int32,
) -> Euclid where {
  proof_require: p > 0,
  proof_ensure: res => 0 <= res.r && res.r < p && res.q * p + res.r == a,
} {
  let r0 = mod_pos(a, p) // 合約：0 ≤ r0 < p
  let q = (a - r0) / p
  Euclid::{ q, r: r0, }
}

///|
/// 定理 T3：2^n ≥ 1，結構遞歸 + 終止量 n。
pub fn pow2_rec(
  n : Int32,
) -> Int32 where {
  proof_require: n >= 0,
  proof_decrease: n,
  proof_ensure: result => result >= 1,
} {
  if n == 0 {
    1
  } else {
    let half = pow2_rec(n / 2)
    let sq = half * half
    if n % 2 == 0 {
      sq
    } else {
      2 * sq
    }
  }
}

///|
/// 定理 T4：快速冪（repeated squaring，遞歸版）結果恆為 [0, p) 的殘基。
pub fn pow_mod(
  base : Int32,
  exp : Int32,
  p : Int32,
) -> Int32 where {
  proof_require: p > 0 && exp >= 0,
  proof_decrease: exp,
  proof_ensure: result => 0 <= result && result < p,
} {
  if exp == 0 {
    mod_pos(1, p) // p ≠ 0（由 p > 0）
  } else {
    let half = pow_mod(base, exp / 2, p) // 範圍：由合約
    let sq = mod_pos(half * half, p) // 範圍：由合約
    if exp % 2 == 0 {
      sq
    } else {
      mod_pos(sq * mod_pos(base, p), p) // 兩層範圍：由合約
    }
  }
}
