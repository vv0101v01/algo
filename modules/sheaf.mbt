// 模層（module sheaf）底層演算法：模的局部化 M_g 與層公理的可計算片段。
//
// 設定：R = FinAlg 有限交換環、M = R-模。基本開集 D(g) 上的截面層值
// 為局部化 M_g。計算模型（HIT 商）：M_g = (M × ℕ) / ~，其中
//   (x, k) ~ (g·x, k+1)  （生成元；一般 (x,k) ~ (y,l) ⟺ g^l·x = g^k·y）
// 由有限圖的連通分量（並查集）精確求得——即集合商 HIT 的類計算。
//
// 層公理（README 公式）：恆等限制 M_1 ≅ M；限制沿複合；粘合唯一性。
// 此處以可驗片段呈現：g 單位 ⇒ |M_g| = |M|；g 幂零/扭率 ⇒ M_g 壓縮；
// g = 0 ⇒ M_0 = 0。

///|
fn mod_index(p : Int32, dim : Int32, x : Array[Int32]) -> Int32 {
  let mut idx = 0
  let mut place = 1
  for i in 0..<dim {
    idx = idx + @num.mod_pos(x[i], p) * place
    place = place * p
  }
  idx
}

///|
fn mod_elem_at(p : Int32, dim : Int32, idx : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut v = idx
  for _i in 0..<dim {
    out.push(@num.mod_pos(v, p))
    v = v / p
  }
  out
}

///|
fn uf_find(parent : Array[Int32], a : Int32) -> Int32 {
  let mut cur = a
  while parent[cur] != cur {
    cur = parent[cur]
  }
  // 路徑壓縮
  let mut c = a
  while parent[c] != cur {
    let nxt = parent[c]
    parent[c] = cur
    c = nxt
  }
  cur
}

///|
fn uf_union(parent : Array[Int32], a : Int32, b : Int32) -> Unit {
  let ra = uf_find(parent, a)
  let rb = uf_find(parent, b)
  if ra != rb {
    parent[rb] = ra
  }
}

///|
/// 局部化類數（算法）：`|M_g|` = 生成圖 `(x,k)—(g·x,k+1)` 的連通分量數。
/// 規模守衛：`|M| ≤ 64`（K = |M| 足使穩定：軌道長 ≤ |M| 必入環）。
/// 定理（恆等限制）：`g = 1 ⇒ |M_g| = |M|`（`M_1 ≅ M`，層公理之恆等性）。
/// 定理（零元）：`g = 0 ⇒ |M_0| = 1`（全部壓至 0）。
/// 定理（g-扭率消沒）：`g^k·x = 0 ⇒ (x,0)` 與 `(0,1)` 同類 — 扭率元在 M_g 中為 0。
pub fn mod_localize_size(m : FinModule, g : Array[Int32]) -> Int32 {
  let p = m.alg.p
  let dim = m.dim
  let n = @num.power_int(p, dim)
  if n > 64 || n < 1 {
    abort("mod_localize_size: module size must be in [1, 64]")
  }
  let parent = mod_build_parent(m, g)
  let mut classes = 0
  let total = parent.length()
  for i in 0..<total {
    if uf_find(parent, i) == i {
      classes = classes + 1
    }
  }
  classes
}

///|
/// 元素在局部化中的類 id（`(x, 0)` 的連通分量根）——供限制映射/粘合取用。
pub fn mod_localize_class_of(
  m : FinModule,
  g : Array[Int32],
  x : Array[Int32],
) -> Int32 {
  let p = m.alg.p
  let dim = m.dim
  let n = @num.power_int(p, dim)
  if n > 64 || n < 1 {
    abort("mod_localize_class_of: module size must be in [1, 64]")
  }
  let parent = mod_build_parent(m, g)
  let xi = mod_index(p, dim, x)
  uf_find(parent, xi)
}

///|
/// 生成圖並查集構建（含頂層飽和邊）：節點 `(k, x)`、邊 `(x,k)—(g·x,k+1)`，
/// 另在 `k = k_max` 層加 `(y, K)—(g·y, K)` 飽和邊（等價於無窮塔中
/// `(y,K) ~ (g^t y, K+t) → (0, K+t)` 的有限截斷——保證 g-冪零軌道全部合流）。
fn mod_build_parent(m : FinModule, g : Array[Int32]) -> Array[Int32] {
  let p = m.alg.p
  let dim = m.dim
  let n = @num.power_int(p, dim)
  if n > 64 || n < 1 {
    abort("mod_localize: module size must be in [1, 64]")
  }
  let k_max = n // 軌道穩定界
  let total = (k_max + 1) * n
  let parent : Array[Int32] = []
  for i in 0..<total {
    parent.push(i)
  }
  for k in 0..<k_max {
    for xi in 0..<n {
      let x = mod_elem_at(p, dim, xi)
      let gx = act(m, g, x)
      let gi = mod_index(p, dim, gx)
      uf_union(parent, k * n + xi, (k + 1) * n + gi)
    }
  }
  // 頂層飽和：(xi, K) — (g·xi, K)
  for xi in 0..<n {
    let x = mod_elem_at(p, dim, xi)
    let gx = act(m, g, x)
    let gi = mod_index(p, dim, gx)
    uf_union(parent, k_max * n + xi, k_max * n + gi)
  }
  parent
}
