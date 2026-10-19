///|
/// 範疇化（categorification）擴展 —— 把集合層的結構提升到範疇/群胚層，
/// 並給出反降（decategorification）與 K-理論橋樑。每個建構附定義、
/// 定理與演算法；正確性由計算測試（公理窮舉 + 性質）給出證據。
///
/// 本檔交付：
///   1. `Category` / `Groupoid` 字典（異質 hom 的閉包字典編碼）
///   2. `delooping_zn`      —— 群的去圈（一物體群胚 B(ℤ/n)），π₁ 定理
///   3. `path_category`     —— 圖上的自由範疇（路徑範疇）+ 長度函子
///   4. `graph_components`  —— π₀ 演算法（連通分量）+ 可達性定理
///   5. `PartitionGroupoid` —— 分割群胚、π₀、群胚基數定理 Σ 1/|Aut| = #π₀
///   6. `Frac` / 群胚基數   —— 有理數 cardinality（反降的像）
///   7. `KClass` (Grothendieck) —— 交換幺半群 M → 群 K(M) 的泛性定理
///   8. `yoneda_nat_count`  —— 有限 Yoneda 定理 Nat(h¹, F) ≅ F(1)（[1] 上）

///==========================================================================
/// 1. 範疇 / 群胚字典
///==========================================================================

///|
/// 定義（範疇）：資料 `(Obj, Hom, id, ∘, src, tgt)`，其中
/// `src, tgt : Hom → Obj`，`id(v) : v → v`，
/// `compose(g, f) = g ∘ f`（**先 f 後 g**，要求 `tgt(f) = src(g)`），
/// 並滿足結合律 `(h ∘ g) ∘ f = h ∘ (g ∘ f)` 與單位律
/// `id(tgt f) ∘ f = f = f ∘ id(src f)`。
///
/// 編碼：MoonBit trait 無異質 hom 的關聯類型，故以**閉包字典**
/// （struct of closures）表示 —— 具體熱路徑（數值層）仍全部走
/// 靜態分發；字典僅承載範疇層小規模組合子。律以 `assoc_ok` /
/// `unit_ok` 可計算檢查（測試窮舉/抽樣驗證）。
pub struct Category[Obj, Hom] {
  id : (Obj) -> Hom
  src : (Hom) -> Obj
  tgt : (Hom) -> Obj
  /// `compose(g, f)`：圖式順序，先 `f` 後 `g`。
  compose : (Hom, Hom) -> Hom
  eq : (Hom, Hom) -> Bool
}

///|
/// 定義（群胚 groupoid）：範疇中每個態射可逆；
/// `inv(f) ∘ f = id(src f)`、`f ∘ inv(f) = id(tgt f)`。
pub struct Groupoid[Obj, Hom] {
  cat : Category[Obj, Hom]
  inv : (Hom) -> Hom
}

///|
/// 結合律檢查（調用方保證 f,g,h 類型接合：`tgt f = src g`、`tgt g = src h`）。
pub fn[Obj, Hom] assoc_ok(
  c : Category[Obj, Hom],
  f : Hom,
  g : Hom,
  h : Hom,
) -> Bool {
  let left = (c.compose)((c.compose)(h, g), f)
  let right = (c.compose)(h, (c.compose)(g, f))
  (c.eq)(left, right)
}

///|
/// 單位律檢查：`id(tgt f) ∘ f = f = f ∘ id(src f)`。
pub fn[Obj, Hom] unit_ok(c : Category[Obj, Hom], f : Hom) -> Bool {
  let ft = (c.tgt)(f)
  let fs = (c.src)(f)
  (c.eq)((c.compose)((c.id)(ft), f), f) && (c.eq)((c.compose)(f, (c.id)(fs)), f)
}

///|
/// 逆元律檢查（群胚）：左右逆 + 保持端點。
pub fn[Obj, Hom] inv_ok(g : Groupoid[Obj, Hom], f : Hom) -> Bool {
  // 端點保持由 id 方程的型別（src/tgt 參數）承載；Hom 層四式 = 左右逆律。
  let fi = (g.inv)(f)
  let c = g.cat
  (c.eq)((c.compose)(fi, f), (c.id)((c.src)(f))) &&
  (c.eq)((c.compose)(f, fi), (c.id)((c.tgt)(f)))
}

///==========================================================================
/// 2. 去圈（delooping）：B(ℤ/n)
///==========================================================================

///|
/// 定義（去圈）：交換群 `(G, ·, e)` 的**一物體範疇** `B(G)`：
/// 物體唯一、`Hom(*) = G`、合成 = 群乘法、`id = e`。
///
/// 定理（π₁ 恢復 / 反降）：`B(G)` 的自同構幺半群 = G —— 即
/// 「範疇化再取 hom」回到原群（decategorification 的 unit）。
/// 這裡 `G = ℤ/n`（加法群），合成 `g ∘ f = (g + f) mod n`。
/// 定理（群胚版）：取 `inv(f) = −f mod n` 得群胚 `B(ℤ/n)`，
/// 滿足三條逆元律（由 `inv_ok` 窮舉驗證）。
pub fn delooping_zn(n : Int32) -> Category[Int32, Int32] {
  if n < 1 {
    abort("delooping_zn: n must be >= 1")
  }
  Category::{
    id: fn(_v : Int32) { 0 },
    src: fn(_f : Int32) { 0 },
    tgt: fn(_f : Int32) { 0 },
    compose: fn(g : Int32, f : Int32) { @num.mod_pos(g + f, n) },
    eq: fn(a : Int32, b : Int32) { a == b },
  }
}

///|
/// `B(ℤ/n)` 的群胚版本（逆 = 取負）。
pub fn delooping_zn_groupoid(n : Int32) -> Groupoid[Int32, Int32] {
  Groupoid::{
    cat: delooping_zn(n),
    inv: fn(f : Int32) { @num.mod_pos(-f, n) },
  }
}

///==========================================================================
/// 3. 自由範疇：路徑範疇 + 長度函子
///==========================================================================

///|
/// 有向圖：`n` 個頂點 `0..n-1`，`edges[i] = (u, v)`。
pub(all) struct Graph {
  n : Int32
  edges : Array[(Int32, Int32)]
} derive(Debug)

///|
/// 路徑：邊索引序列，自帶端點（空路徑 = 恆等態射，端點即物體）。
pub(all) struct Path {
  edges : Array[Int32]
  from : Int32
  to : Int32
} derive(Debug)

///|
/// 整數序列相等（路徑合成律用）。
fn ipath_eq(a : Array[Int32], b : Array[Int32]) -> Bool {
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

///|
/// 定義（自由範疇）：圖 `G` 的路徑範疇 `Path(G)`：
/// 物體 = 頂點；態射 `x → y` = 從 x 到 y 的**邊序列**（路徑）；
/// 合成 = 序列串接；恆等 = 空路徑。
///
/// 定理（自由性 / 泛性）：對任意範疇 `C` 與圖映射（頂點、邊指定），
/// 存在**唯一**函子 `Path(G) → C` 延拓該指定 —— 合成律在 `Path(G)`
/// 中就是列表串接結合律 `(f++g)++h = f++(g++h)`（結構相等，由
/// 測試窮舉驗證），故延拓函子良定（見測試 3：到 `B(ℤ/n)` 的加權函子）。
pub fn path_category(g : Graph) -> Category[Int32, Path] {
  Category::{
    id: fn(v : Int32) { Path::{ edges: [], from: v, to: v, } },
    src: fn(p : Path) { p.from },
    tgt: fn(p : Path) { p.to },
    compose: fn(g2 : Path, f : Path) {
      if f.to != g2.from {
        abort("path_category: type mismatch in composition")
      }
      let e : Array[Int32] = []
      for x in f.edges {
        if x < 0 || x >= g.edges.length() {
          abort("path_category: edge index out of graph range")
        }
        e.push(x)
      }
      for x in g2.edges {
        if x < 0 || x >= g.edges.length() {
          abort("path_category: edge index out of graph range")
        }
        e.push(x)
      }
      Path::{ edges: e, from: f.from, to: g2.to, }
    },
    eq: fn(a : Path, b : Path) {
      a.from == b.from && a.to == b.to && ipath_eq(a.edges, b.edges)
    },
  }
}

///|
/// 路徑長度（邊數）。
pub fn path_len(p : Path) -> Int32 {
  p.edges.length()
}

///|
/// 定理（長度函子）：`len : Path(G) → (ℕ, +, 0)` 是函子：
/// `len(g ∘ f) = len f + len g`、`len(id_v) = 0`。
/// 檢查經由範疇字典的合成（測試中調用 `path_category(g).compose`），
/// 這裡提供定律右端的合成長度（`f ++ g` 的邊數）。
pub fn compose_len(f : Path, g : Path) -> Int32 {
  if f.to != g.from {
    abort("compose_len: type mismatch")
  }
  f.edges.length() + g.edges.length()
}

///|
/// 加權函子：圖映射 `w : E → ℤ/n` 延拓到 `W : Path(G) → B(ℤ/n)`，
/// `W(p) = Σ_{e ∈ p} w(e) mod n`（自由範疇泛性的存在性實例）。
/// 定理：`W(g ∘ f) = W(f) + W(g)`、`W(id) = 0`（模 n 交換群）。
pub fn path_weighted(g : Graph, w : Array[Int32], n : Int32, p : Path) -> Int32 {
  if w.length() != g.edges.length() {
    abort("path_weighted: weight vector length must equal edge count")
  }
  let mut acc = 0
  for ei in p.edges {
    acc = @num.mod_pos(acc + w[ei], n)
  }
  acc
}

///==========================================================================
/// 4. π₀ 演算法：連通分量
///==========================================================================

///|
/// 定義（π₀）：群胚的**同構類**集合 `π₀(G) = G / ≅`；
/// 對路徑範疇，`π₀(Path(G))` = 圖的連通分量（經典）。
///
/// 演算法：BFS 染色（`O(V + E)`）—— 未訪問頂點開新分量，沿邊蔓延。
/// 定理（正確性）：`comp[u] = comp[v]` ⟺ 存在 u→v 的路徑（互為充要）——
/// BFS 性質直接給出；由測試與 `graph_reachable`（獨立 BFS 可達性）
/// 交叉驗證 + 樣例斷言。
pub fn graph_components(g : Graph) -> Array[Int32] {
  let comp : Array[Int32] = []
  for _v in 0..<g.n {
    comp.push(-1)
  }
  let mut c = 0
  for s in 0..<g.n {
    if comp[s] != -1 {
      continue
    }
    // BFS
    let q : Array[Int32] = []
    q.push(s)
    comp[s] = c
    let mut head = 0
    while head < q.length() {
      let u = q[head]
      head = head + 1
      for e in g.edges {
        let (a, b) = e
        let mut other = -1
        if a == u {
          other = b
        } else if b == u {
          other = a
        }
        if other != -1 && comp[other] == -1 {
          comp[other] = c
          q.push(other)
        }
      }
    }
    c = c + 1
  }
  comp
}

///|
/// 可達性（BFS）：是否存在 `a → b` 的有向路徑？（無向化：兩向蔓延 ——
/// 對應 fundamental groupoid 的 morphism 存在性；這裡圖按**無向**連通
/// 判定 π₀，與 `graph_components` 的雙向蔓延一致）。
pub fn graph_reachable(g : Graph, a : Int32, b : Int32) -> Bool {
  if a == b {
    return true
  }
  let seen : Array[Bool] = []
  for _v in 0..<g.n {
    seen.push(false)
  }
  let q : Array[Int32] = []
  q.push(a)
  seen[a] = true
  let mut head = 0
  while head < q.length() {
    let u = q[head]
    head = head + 1
    for e in g.edges {
      let (x, y) = e
      let mut other = -1
      if x == u {
        other = y
      } else if y == u {
        other = x
      }
      if other != -1 && !seen[other] {
        if other == b {
          return true
        }
        seen[other] = true
        q.push(other)
      }
    }
  }
  false
}

///==========================================================================
/// 5. 分割群胚 + 群胚基數（反降）
///==========================================================================

///|
/// 定義（有理數）：`Frac = { n/d : d > 0 }`，加法後約分
/// （`gcd` 歸一、符號入分子）—— 反降 `|G| ∈ ℚ` 的承載。
pub(all) struct Frac {
  num : Int32
  den : Int32
} derive(Debug, Eq)

///|
/// 有理數構造（自動約分）；`den != 0`。
pub fn frac(num : Int32, den : Int32) -> Frac {
  if den == 0 {
    abort("frac: denominator must be nonzero")
  }
  let mut n = num
  let mut d = den
  if d < 0 {
    n = -n
    d = -d
  }
  let g = @num.gcd(n, d)
  let gg = if g <= 1 { 1 } else { g }
  Frac::{ num: n / gg, den: d / gg, }
}

///|
/// 分數加法（先通分後約分；小規模，元素適度）。
pub fn frac_add(a : Frac, b : Frac) -> Frac {
  frac(a.num * b.den + b.num * a.den, a.den * b.den)
}

///|
/// 定義（分割群胚）：集合 `X = {0..N-1}` 與等價關係（分割）給出群胚：
/// `Hom(x, y)` 單元素（當 x ~ y）否則空；合成 = 關係傳遞。
/// 這裡以 `cls[x]`（塊標籤）給出分割。
pub(all) struct PartitionGroupoid {
  cls : Array[Int32]
} derive(Debug, Eq)

///|
/// 同構判定：`x ≅ y ⟺ cls[x] = cls[y]`（同塊內態射可逆）。
pub fn PartitionGroupoid::is_iso(self : Self, x : Int32, y : Int32) -> Bool {
  self.cls[x] == self.cls[y]
}

///|
/// π₀：同構類（相異塊標籤，升序）。
pub fn PartitionGroupoid::pi0(self : Self) -> Array[Int32] {
  let out : Array[Int32] = []
  for c in self.cls {
    let mut seen = false
    for o in out {
      if o == c {
        seen = true
      }
    }
    if !seen {
      out.push(c)
    }
  }
  out
}

///|
/// 定理（同構是等價關係）：群胚中 `≅` 自反（`id`）、對稱（`inv`）、
/// 傳遞（`∘`）—— 由群胚公理直接給出；此處以字典律的可計算形式驗證。
pub fn PartitionGroupoid::iso_is_equivalence(self : Self) -> Bool {
  let n = self.cls.length()
  for x in 0..<n {
    if !self.is_iso(x, x) {
      return false
    }
    for y in 0..<n {
      if self.is_iso(x, y) != self.is_iso(y, x) {
        return false
      }
      for z in 0..<n {
        if self.is_iso(x, y) && self.is_iso(y, z) && !self.is_iso(x, z) {
          return false
        }
      }
    }
  }
  true
}

///|
/// 定理（π₀ 計數交叉驗證）：`#π₀ = `同構矩陣 `R[x][y] = (x ≅ y)`
/// 的**不同行數** —— 與 `pi0()`（標籤掃描）是兩條獨立演算法，
/// 輸出必相等（測試斷言）。行數重複 ⇔ 兩元素同塊 ⇔ 行相等。
pub fn PartitionGroupoid::iso_class_count(self : Self) -> Int32 {
  let n = self.cls.length()
  let mut cnt = 0
  let seen : Array[Bool] = []
  for _i in 0..<n {
    seen.push(false)
  }
  for x in 0..<n {
    if seen[x] {
      continue
    }
    // 標記與 x 行相同的所有 y（同行 = 同構類）
    for y in 0..<n {
      let mut same = true
      for z in 0..<n {
        if self.is_iso(x, z) != self.is_iso(y, z) {
          same = false
        }
      }
      if same {
        seen[y] = true
      }
    }
    cnt = cnt + 1
  }
  cnt
}

///|
/// 定理（群胚基數 / decategorification）：有限群胚 `G` 的基數
/// `|G| = Σ_{x ∈ π₀ 代表} 1 / |Aut(x)|`；對分割群胚，
/// `Aut(x) = 塊 C[x]`，故 `|G| = Σ_類 |C| · (1/|C|) = #π₀`。
/// 即 **反降把群胚打回其 π₀ 的個數**（有理數層的「物件計數」）。
/// 演算法：逐元素累加 `1/|cls(x)|` 再約分。
pub fn PartitionGroupoid::groupoid_cardinality(self : Self) -> Frac {
  let mut acc = Frac::{ num: 0, den: 1, }
  let n = self.cls.length()
  for x in 0..<n {
    let mut sz = 0
    for y in 0..<n {
      if self.cls[y] == self.cls[x] {
        sz = sz + 1
      }
    }
    if sz == 0 {
      abort("groupoid_cardinality: empty class impossible")
    }
    acc = frac_add(acc, frac(1, sz))
  }
  acc
}

///|
/// 分割群胚的群胚字典（Hom = 端點對；只對同塊態射調用合成）。
pub fn PartitionGroupoid::as_groupoid(
  self : Self,
) -> Groupoid[Int32, (Int32, Int32)] {
  let _ = self
  Groupoid::{
    cat: Category::{
      id: fn(v : Int32) { (v, v) },
      src: fn(p : (Int32, Int32)) { p.0 },
      tgt: fn(p : (Int32, Int32)) { p.1 },
      compose: fn(g2 : (Int32, Int32), f : (Int32, Int32)) {
        if f.1 != g2.0 {
          abort("partition groupoid: no such morphism")
        }
        (f.0, g2.1)
      },
      eq: fn(a : (Int32, Int32), b : (Int32, Int32)) {
        a.0 == b.0 && a.1 == b.1
      },
    },
    inv: fn(f : (Int32, Int32)) { (f.1, f.0) },
  }
}

///==========================================================================
/// 6. Grothendieck 群 K(M)
///==========================================================================

///|
/// 定義（Grothendieck 群）：交換幺半群 `M`（此處 `M = (ℕ, +)`）的
/// `K(M) = (M × M) / ~`，`(a, b) ~ (c, d) ⟺ a + d = b + c`；
/// 類 `[a, b] ↔ a − b`，`[a] + [b] = [a + b]`（分量相加）。
///
/// 定理（泛性）：對任意群 `H` 與幺半群同態 `f : M → H`，存在**唯一**
/// 群同態 `f̃ : K(M) → H` 使 `f̃([m]) = f(m)`；交換圖
/// `f̃([a, b]) = f(a) − f(b)`。
/// 這裡以 `M = ℕ`、`H = ℤ/n`、`f(m) = c·m mod n` 實例化（測試：
/// 同態性 + 交換圖兩式）。
pub(all) struct KClass {
  p : Int32
  q : Int32
} derive(Debug)

///|
/// K-類相等：`[p,q] = [p',q'] ⟺ p + q' = q + p'`（交叉條件）。
pub fn k_eq(a : KClass, b : KClass) -> Bool {
  a.p + b.q == a.q + b.p
}

///|
/// K(M) 加法（幺半群直積分量相加）。
pub fn k_add(a : KClass, b : KClass) -> KClass {
  KClass::{ p: a.p + b.p, q: a.q + b.q, }
}

///|
/// K(M) 負元（`[p,q]⁻¹ = [q,p]`）。
pub fn k_neg(a : KClass) -> KClass {
  KClass::{ p: a.q, q: a.p, }
}

///|
/// 同構 `K(ℕ) ≅ ℤ`：`[p,q] ↦ p − q`（保加法雙射；測試驗證）。
pub fn k_to_int(a : KClass) -> Int32 {
  a.p - a.q
}

///|
/// 泛性實例：`f(m) = c·m (mod n)` 誘導群同態 `f̃ : K(ℕ) → ℤ/n`，
/// `f̃([p,q]) = c·(p − q) mod n`。
pub fn k_induced(n : Int32, c : Int32, a : KClass) -> Int32 {
  @num.mul_mod(@num.mod_pos(c, n), @num.mod_pos(k_to_int(a), n), n)
}

///==========================================================================
/// 7. 有限 Yoneda：walking arrow [1]
///==========================================================================

///|
/// 定義（函子範疇 [1] 上的預層）：`[1] = (0 → 1)`，`F : [1]^op → FinSet`
/// 由 `(X₀, X₁, φ : X₁ → X₀)` 給出（`φ = F(u)` 沿 `u : 0 → 1` 反變）。
/// 對 `h¹ = Hom(−, 1)`（可表函子）：
/// `h¹(0) = Hom(0,1) = {u}`、`h¹(1) = Hom(1,1) = {id}`，
/// `h¹(u)(id) = u`。
///
/// 定理（有限 Yoneda）：`Nat(h¹, F) ≅ F(1) = X₁` —— 自然族
/// `(α₀ : h¹(0) → X₀, α₁ : h¹(1) ↔ {·} → X₁)` 的交換條件
/// `φ ∘ α₁ = α₀ ∘ h¹(u)` 把 `α₀` 唯一決定為 `φ(α₁(id))`，
/// 故自然雙射 `α₁(id) ↦ (α₀, α₁)`，計數 `|Nat| = |X₁|`。
///
/// 演算法：線性枚舉全部 `(a ∈ X₀, b ∈ X₁)` 對，數出滿足
/// `φ(b) = a` 者（每個 b 恰好貢獻一個 a）。
pub fn yoneda_nat_count(
  x0_len : Int32,
  x1_len : Int32,
  phi : Array[Int32],
) -> Int32 {
  if phi.length() != x1_len {
    abort("yoneda_nat_count: phi length must equal |X1|")
  }
  let mut cnt = 0
  for b in 0..<x1_len {
    if phi[b] < 0 || phi[b] >= x0_len {
      abort("yoneda_nat_count: phi out of range")
    }
    for a in 0..<x0_len {
      if phi[b] == a {
        cnt = cnt + 1
      }
    }
  }
  cnt
}

///|
/// Yoneda 雙射的正向：`b = α₁(id) ↦ (φ(b), b)`（自然族的參數化）。
/// 定理：此映射為雙射（測試：正向自然性 + 反向 recover）。
pub fn yoneda_fwd(
  x1_len : Int32,
  phi : Array[Int32],
  b : Int32,
) -> (Int32, Int32) {
  if b < 0 || b >= x1_len {
    abort("yoneda_fwd: index out of range")
  }
  (phi[b], b)
}

///|
/// 反演：自然族 `(a, b)` 必須滿足 `a = φ(b)`（良定），以 b 為像。
pub fn yoneda_bwd(
  _x0_len : Int32,
  phi : Array[Int32],
  pair : (Int32, Int32),
) -> Int32 {
  let (a, b) = pair
  if phi[b] != a {
    abort("yoneda_bwd: not a natural transformation")
  }
  b
}
