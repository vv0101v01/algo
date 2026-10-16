// 對偶模、雙對偶維數、扭率子模（上輪遺漏的模論演算法）。

///|
/// 給定向量在環上的作用：`r·x = Σ_i r_i · (e_i · x)`。
fn act(m : FinModule, r : Array[Int32], x : Array[Int32]) -> Array[Int32] {
  let p = m.alg.p
  let mut acc : Array[Int32] = []
  for _k in 0..<m.dim {
    acc.push(0)
  }
  for i in 0..<m.alg.dim {
    let y = m.action[i].apply(x)
    let ri = if i < r.length() { r[i] } else { 0 }
    acc = @linalg.vec_add(p, acc, @linalg.vec_scale(p, ri, y))
  }
  acc
}

///|
/// 對偶模維數（算法）：`dual_dim(M) = dim_k Hom_R(M, R)`。
/// 定理（自由模自對偶）：`Hom(R^n, R) ≅ R^n`，故 `dual_dim(R^n) = n · dim_k R`。
/// 定理（循環模對偶 = 零化子）：`Hom(R/I, R) ≅ Ann_R(I)`（映射 `φ ↦ φ(1)` 互逆），
/// 故 `dual_dim(R/I) = dim_k Ann(I)`；見性質測試逐例驗證。
pub fn dual_dim(m : FinModule) -> Int32 {
  hom_space(m, FinModule::free(m.alg, 1)).length()
}

///|
/// 理想的 `k`-維數：`|I| = p^d` 時為 `d`（否則 −1，防呆）。
pub fn ideal_kdim(i : @finite.FinIdeal) -> Int32 {
  let mut n = 1
  let mut d = 0
  let p = i.alg.p
  while n < i.members.length() {
    n = n * p
    d = d + 1
  }
  if n == i.members.length() {
    d
  } else {
    -1
  }
}

///|
/// 元素扭率判定：`x` 扭率 ⟺ `Ann(x) ⊋ {0}`（存在 `r ≠ 0` 使 `r·x = 0`）。
pub fn is_torsion_elem(m : FinModule, x : Array[Int32]) -> Bool {
  let zero = m.alg.zero_elem() // 長度 dim_alg ≠ dim_m — 用顯式零
  let z : Array[Int32] = []
  for _i in 0..<m.dim {
    z.push(0)
  }
  for r in m.alg.all_elements() {
    if @linalg.vec_eq(r, zero) {
      continue
    }
    if @linalg.vec_eq(act(m, r, x), z) {
      return true
    }
  }
  false
}

///|
/// 扭率子模 `tor(M) = { x ∈ M : Ann(x) ≠ 0 }`（枚舉，帶規模守衛）。
/// 定理：`tor(M)` 是子模；`M/tor(M)` 扭率自由；`tor(M) = 0 ⟺ M` 扭率自由。
pub fn torsion_elements(m : FinModule) -> Array[Array[Int32]] {
  let p = m.alg.p
  if @num.power_int(p, m.dim) > 4096 {
    abort("torsion_elements: module too large (cap 4096 elements)")
  }
  let out : Array[Array[Int32]] = []
  for x in @linalg.enumerate_vectors(p, m.dim) {
    if is_torsion_elem(m, x) {
      out.push(x)
    }
  }
  out
}

///|
/// 扭率自由判定：扭率子模 `tor(M) = {0}`（即不存在非零扭率元）。
pub fn is_torsion_free(m : FinModule) -> Bool {
  let zero : Array[Int32] = []
  for _i in 0..<m.dim {
    zero.push(0)
  }
  for x in torsion_elements(m) {
    if !@linalg.vec_eq(x, zero) {
      return false
    }
  }
  true
}
