// 連續模（逆向系統與逆極限）——上輪遺漏的「連續模」演算法。
//
// 有限塔上的逆極限：線程 `(x_0, …, x_{n-1})` 滿足 `x_t = bond_t(x_{t+1})`；
// 無限塔（如 `R ← R/I ← R/I² ← …` 的 p-adic 完備化）由本資料結構的
// 有限截斷逼近：`lim R/I^n = R̂`，其元素為相容線程（無限情況見 README 公式）。

///|
/// 有限逆向系統 `X_0 ← X_1 ← … ← X_{n-1}`：
/// `bonds[t]` 是函數表 `X_{t+1} → X_t`（`bonds[t][x] ∈ [0, sizes[t])`）。
pub(all) struct InvSystem {
  sizes : Array[Int32]
  bonds : Array[Array[Int32]]
} derive(Debug)

///|
/// 良構判定：`bonds` 比 `sizes` 少一（有 n−1 條鍵）、每條鍵函數值落在下層。
pub fn InvSystem::validate(self : Self) -> Bool {
  if self.bonds.length() + 1 != self.sizes.length() {
    return false
  }
  if self.sizes.length() == 0 {
    return false
  }
  for t in 0..<self.bonds.length() {
    let b = self.bonds[t]
    if b.length() != self.sizes[t + 1] {
      return false
    }
    for v in b {
      if v < 0 || v >= self.sizes[t] {
        return false
      }
    }
  }
  true
}

///|
/// 逆極限線程枚舉（算法）：自頂層掃描，逐層用鍵表下推。
/// 輸出每個線程為 `[x_{n-1}, x_{n-2}, …, x_0]`。
/// 定理（有限塔）：投影 `lim → X_{n-1}` 是雙射，故 `|lim| = |X_{n-1}|`；
/// 而對無限塔 `lim ↪ ∏ X_t` 為真子集（相容性非自動）。
pub fn InvSystem::limit_threads(self : Self) -> Array[Array[Int32]] {
  if !self.validate() {
    abort("InvSystem::limit_threads: invalid system")
  }
  let n = self.sizes.length()
  let top = self.sizes[n - 1]
  if top > 100000 {
    abort("InvSystem::limit_threads: top stage too large")
  }
  let out : Array[Array[Int32]] = []
  for x in 0..<top {
    let thread : Array[Int32] = []
    thread.push(x)
    let mut cur = x
    let mut t = n - 2
    while t >= 0 {
      cur = self.bonds[t][cur]
      thread.push(cur)
      t = t - 1
    }
    out.push(thread)
  }
  out
}

///|
/// 投影滿射性（算法）：鍵複合 `X_{n-1} → X_t` 的像是否覆蓋 `X_t`。
/// 定理（Mittag-Leffler 於有限塔）：全體鍵滿射 ⟺ 全體投影滿射
/// （複合滿射仍是滿射；反向逐層抬升）。見性質測試。
pub fn InvSystem::projection_surjective(self : Self, t : Int32) -> Bool {
  if !self.validate() || t < 0 || t >= self.sizes.length() {
    return false
  }
  let n = self.sizes.length()
  // 從頂層沿鍵複合到 t：收集像集
  let image : Array[Bool] = []
  for _i in 0..<self.sizes[t] {
    image.push(false)
  }
  let top = self.sizes[n - 1]
  for x in 0..<top {
    let mut cur = x
    let mut s = n - 2
    while s >= t {
      cur = self.bonds[s][cur]
      s = s - 1
    }
    image[cur] = true
  }
  for b in image {
    if !b {
      return false
    }
  }
  true
}

///|
/// 鍵單射性（算法）：`bonds[t]` 是否為單射（無兩點同像）。
/// 定理：有限集合上，全體鍵單射且頂層非空 ⟺ 各投影單射。
pub fn InvSystem::bond_injective(self : Self, t : Int32) -> Bool {
  if !self.validate() || t < 0 || t >= self.bonds.length() {
    return false
  }
  let seen : Array[Bool] = []
  for _i in 0..<self.sizes[t] {
    seen.push(false)
  }
  for v in self.bonds[t] {
    if seen[v] {
      return false
    }
    seen[v] = true
  }
  true
}
