// 範疇論底層演算法：有限函子空間、伴隨（Hom 形式）的等價證據。
//
// 定理（乘積伴隨）：`Hom(X, Y × Z) ≅ Hom(X, Y) × Hom(X, Z)`
//   fwd(f) = (π₁∘f, π₂∘f)，bwd(g,h)(x) = (g x, h x)——互逆（逐點驗證）。
// 定理（餘積伴隨）：`Hom(Y ⊔ Z, X) ≅ Hom(Y, X) × Hom(Z, X)`。
// 這些是「Hom 搬運」等價：伴隨對的單位/餘單位由 roundtrip 見證給出。

///|
/// 有限集函子空間枚舉：全部函數 `[0,nx) → [0,ny)`（以值表陣列表示）。
/// 守衛：`ny^nx ≤ 100000`。
pub fn enumerate_functions(nx : Int32, ny : Int32) -> Array[Array[Int32]] {
  if nx < 0 || ny < 0 {
    abort("enumerate_functions: negative size")
  }
  let mut total = 1
  for _i in 0..<nx {
    total = total * ny
    if total > 100000 {
      abort("enumerate_functions: function space too large")
    }
  }
  let out : Array[Array[Int32]] = []
  if nx == 0 {
    out.push([])
    return out
  }
  if ny == 0 {
    return out // X ≠ ∅ 時 Hom(X, ∅) = ∅
  }
  // 混合基數遞增枚舉
  let cur : Array[Int32] = []
  for _i in 0..<nx {
    cur.push(0)
  }
  let mut done = false
  while !done {
    let f : Array[Int32] = []
    for v in cur {
      f.push(v)
    }
    out.push(f)
    // 遞增
    let mut k = nx - 1
    while k >= 0 {
      cur[k] = cur[k] + 1
      if cur[k] < ny {
        break
      }
      cur[k] = 0
      k = k - 1
    }
    if k < 0 {
      done = true
    }
  }
  out
}

///|

///|
/// 乘積伴隨 Hom-等價（定理即程序）：
/// `f : X → Y×Z`（`Y×Z` 元素編碼 `y·|Z|+z`）⟷ `(g : X→Y, h : X→Z)`。
/// 檢查 fwd∘bwd = id 且 bwd∘fwd = id 於全域函子空間（有限精確）。
pub fn curry_equiv_holds(nx : Int32, ny : Int32, nz : Int32) -> Bool {
  // Hom(X, Y×Z)
  let hom_prod = enumerate_functions(nx, ny * nz)
  // Hom(X,Y) × Hom(X,Z)：配對以串接表 [g…|h…] 表示
  let hom_y = enumerate_functions(nx, ny)
  let hom_z = enumerate_functions(nx, nz)
  // bwd ∘ fwd : f ↦ (g,h) ↦ λx.(g x, h x)
  for f in hom_prod {
    let g : Array[Int32] = []
    let h : Array[Int32] = []
    for x in 0..<nx {
      let y = f[x] / nz
      let z = @num.mod_pos(f[x], nz)
      g.push(y)
      h.push(z)
    }
    // λx.(g x, h x) — 重建
    let f2 : Array[Int32] = []
    for x in 0..<nx {
      f2.push(g[x] * nz + h[x])
    }
    if !vec32_eq(f, f2) {
      return false
    }
  }
  // fwd ∘ bwd : (g,h) ↦ f ↦ (g,h)
  for g in hom_y {
    for h in hom_z {
      let f : Array[Int32] = []
      for x in 0..<nx {
        f.push(g[x] * nz + h[x])
      }
      let g2 : Array[Int32] = []
      let h2 : Array[Int32] = []
      for x in 0..<nx {
        g2.push(f[x] / nz)
        h2.push(@num.mod_pos(f[x], nz))
      }
      if !vec32_eq(g, g2) || !vec32_eq(h, h2) {
        return false
      }
    }
  }
  true
}

///|
/// 餘積伴隨 Hom-等價（定理即程序）：
/// `t : Y⊔Z → X`（前 ny 值來自 Y、後 nz 值來自 Z）⟷ `(g : Y→X, h : Z→X)`。
pub fn coprod_hom_equiv_holds(ny : Int32, nz : Int32, nx : Int32) -> Bool {
  let hom_sum = enumerate_functions(ny + nz, nx)
  let hom_y = enumerate_functions(ny, nx)
  let hom_z = enumerate_functions(nz, nx)
  for t in hom_sum {
    let g : Array[Int32] = []
    let h : Array[Int32] = []
    for i in 0..<ny {
      g.push(t[i])
    }
    for j in 0..<nz {
      h.push(t[ny + j])
    }
    // 重建
    let t2 : Array[Int32] = []
    for i in 0..<ny {
      t2.push(g[i])
    }
    for j in 0..<nz {
      t2.push(h[j])
    }
    if !vec32_eq(t, t2) {
      return false
    }
  }
  for g in hom_y {
    for h in hom_z {
      let t : Array[Int32] = []
      for i in 0..<ny {
        t.push(g[i])
      }
      for j in 0..<nz {
        t.push(h[j])
      }
      // 經 fwd 再 bwd
      let g2 : Array[Int32] = []
      let h2 : Array[Int32] = []
      for i in 0..<ny {
        g2.push(t[i])
      }
      for j in 0..<nz {
        h2.push(t[ny + j])
      }
      if !vec32_eq(g, g2) || !vec32_eq(h, h2) {
        return false
      }
    }
  }
  true
}
