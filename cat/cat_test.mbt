// Blackbox tests for `cat`（範疇化）：公理斷言 + 性質（quickcheck）。

///|
/// 隨機取模：共用 `@testutil.det_rand`（跨包唯一測試 PRNG —— 避免重製）。
fn cat_rand(seed : Int32, salt : Int32, m : Int32) -> Int32 {
  @num.mod_pos(@testutil.det_rand(seed, salt), m)
}

///|
/// 定理（去圈 π₁ 恢復）：B(ℤ/n) 的合成律 = ℤ/n 加法群律。
/// 窮舉：結合律 n³ + 單位律 n + 逆元律 n。
test "delooping B(ℤ/6): category + groupoid laws exhaustively" {
  let n = 6
  let c = @cat.delooping_zn(n)
  for f in 0..<n {
    for g in 0..<n {
      for h in 0..<n {
        assert_true(@cat.assoc_ok(c, f, g, h))
      }
    }
    assert_true(@cat.unit_ok(c, f))
  }
  // 合成 = 群乘法（同構恢復：hom 講話回到 (ℤ/6, +)）
  assert_eq((c.compose)(4, 5), 3) // (4+5) mod 6
  assert_eq((c.id)(0), 0)
  let gd = @cat.delooping_zn_groupoid(n)
  for f in 0..<n {
    assert_true(@cat.inv_ok(gd, f))
  }
}

///|
/// 定理（自由範疇 + 長度函子）：路徑合成結合律（列表串接）、恆等 = 空路徑、
/// `len(g∘f) = len f + len g`、`len(id) = 0`。
test "path category: assoc, identity, length functor laws" {
  let g = @cat.Graph::{ n: 4, edges: [(0, 1), (1, 2), (0, 2), (2, 3)], }
  let c = @cat.path_category(g)
  // 可接合三連：0→1→2→3
  let f = @cat.Path::{ edges: [0], from: 0, to: 1, }
  let gg = @cat.Path::{ edges: [1], from: 1, to: 2, }
  let h = @cat.Path::{ edges: [3], from: 2, to: 3, }
  assert_true(@cat.assoc_ok(c, f, gg, h))
  // 恆等律（各物體）
  for v in 0..<4 {
    assert_true(@cat.unit_ok(c, (c.id)(v)))
  }
  // 長度函子
  let fg = (c.compose)(gg, f) // 0→2 via [0,1]
  assert_eq(@cat.path_len(fg), 2)
  assert_eq(@cat.path_len(fg), @cat.path_len(f) + @cat.path_len(gg))
  assert_eq(@cat.path_len((c.id)(2)), 0)
  assert_eq(@cat.compose_len(f, gg), 2)
  // 非法合成（端點不接）應中止 —— 這裡以良定輸入為主，另路徑自定端點
  assert_eq(@cat.path_len(h), 1)
}

///|
/// 定理（自由性泛性的存在側）：任意邊權 `w : E → ℤ/n` 延拓為函子
/// `W : Path(G) → B(ℤ/n)`，`W(g∘f) = W(f) + W(g)`、`W(id) = 0`。
test "free universal property: weighted functor Path(G) -> B(ℤ/n)" {
  let g = @cat.Graph::{ n: 4, edges: [(0, 1), (1, 2), (0, 2), (2, 3)], }
  let n = 5
  let w = [1, 2, 3, 4]
  let c = @cat.path_category(g)
  let f = @cat.Path::{ edges: [0], from: 0, to: 1, }
  let gg = @cat.Path::{ edges: [1], from: 1, to: 2, }
  let fg = (c.compose)(gg, f)
  // 同態律（模 n）
  assert_eq(
    @cat.path_weighted(g, w, n, fg),
    @num.mod_pos(
      @cat.path_weighted(g, w, n, f) + @cat.path_weighted(g, w, n, gg),
      n,
    ),
  )
  // 直接折疊：路徑 [0,1]（邊0→1→2）權 1+2 = 3
  assert_eq(@cat.path_weighted(g, w, n, fg), 3)
  // 恆等 → 0
  assert_eq(
    @cat.path_weighted(g, w, n, @cat.Path::{ edges: [], from: 2, to: 2, }),
    0,
  )
  // 性質：隨機權重、隨機長度路徑（邊序列良定時的同態性）
  @quickcheck.check((seed : Int32) => {
    let nn = 7
    let w2 : Array[Int32] = []
    for i in 0..<g.edges.length() {
      w2.push(cat_rand(seed, i * 17 + 3, nn))
    }
    // 隨機良定路徑：從 0 經 [0,2] 到 2（固定骨架，權隨機）
    let p1 = @cat.Path::{ edges: [0], from: 0, to: 1, }
    let p2 = @cat.Path::{ edges: [1], from: 1, to: 2, }
    let p12 = (c.compose)(p2, p1)
    let lhs = @cat.path_weighted(g, w2, nn, p12)
    let rhs = @num.mod_pos(
      @cat.path_weighted(g, w2, nn, p1) + @cat.path_weighted(g, w2, nn, p2),
      nn,
    )
    lhs == rhs
  })
}

///|
/// 定理（π₀ + 群胚基數反降）：分割群胚 π₀ = 異塊標籤；
/// `|G| = Σ_x 1/|Aut x| = #π₀`（有理數層精確相等）。
test "partition groupoid: pi0, iso-classes, cardinality decategorification" {
  let p = @cat.PartitionGroupoid::{ cls: [0, 0, 1, 1, 1, 2], }
  assert_eq(p.pi0(), [0, 1, 2])
  assert_true(p.is_iso(0, 1))
  assert_false(p.is_iso(0, 2))
  // ≅ 是等價關係 + 兩條獨立 π₀ 計數演算法一致
  assert_true(p.iso_is_equivalence())
  assert_eq(p.pi0().length(), p.iso_class_count())
  // 群胚基數 = #π₀ = 3
  assert_eq(p.groupoid_cardinality(), @cat.frac(3, 1))
  // 性質：隨機分割 → 基數反降定理 + π₀ 分離
  @quickcheck.check((seed : Int32) => {
    let nn = 6
    let cls : Array[Int32] = []
    for i in 0..<nn {
      cls.push(cat_rand(seed + 7, i * 13 + 1, 3)) // 3 塊標籤
    }
    let pp = @cat.PartitionGroupoid::{ cls, }
    let k = pp.pi0().length()
    let card_ok = pp.groupoid_cardinality() == @cat.frac(k, 1)
    let mut sep = true
    for x in 0..<nn {
      for y in 0..<nn {
        if pp.is_iso(x, y) != (cls[x] == cls[y]) {
          sep = false
        }
      }
    }
    let cross = pp.iso_class_count() == k
    card_ok && sep && cross && pp.iso_is_equivalence()
  })
}

///|
/// 定理（π₀ 演算法正確性）：`comp[u] = comp[v]` ⟺ 可達（無向 BFS 意義）。
test "graph components <-> reachability (pi0 of path category)" {
  let g = @cat.Graph::{ n: 5, edges: [(0, 1), (1, 2), (3, 4)], }
  let comp = @cat.graph_components(g)
  assert_eq(comp.length(), 5)
  // {0,1,2} 一塊、{3,4} 一塊
  assert_true(comp[0] == comp[1] && comp[1] == comp[2])
  assert_true(comp[3] == comp[4])
  assert_false(comp[0] == comp[3])
  assert_true(@cat.graph_reachable(g, 0, 2))
  assert_false(@cat.graph_reachable(g, 0, 3))
  assert_true(@cat.graph_reachable(g, 4, 3)) // 無向
  // 性質：隨機圖上兩演算法一致
  @quickcheck.check((seed : Int32) => {
    let nv = 6
    let edges : Array[(Int32, Int32)] = []
    for e in 0..<7 {
      let a = cat_rand(seed, e * 5 + 1, nv)
      let b = cat_rand(seed + 31, e * 9 + 2, nv)
      if a != b {
        edges.push((a, b))
      }
    }
    let gg = @cat.Graph::{ n: nv, edges, }
    let cc = @cat.graph_components(gg)
    let mut ok = true
    for x in 0..<nv {
      for y in 0..<nv {
        if (cc[x] == cc[y]) != @cat.graph_reachable(gg, x, y) {
          ok = false
        }
      }
    }
    ok
  })
}

///|
/// 定理（Grothendieck 泛性）：K(ℕ) ≅ ℤ（k_to_int 保加法）、
/// 誘導同態 `f̃([p,q]) = c·(p−q) mod n` 滿足交換圖 + 同態性。
test "Grothendieck K(ℕ): group laws, Z-isomorphism, universal induced hom" {
  let a = @cat.KClass::{ p: 5, q: 3, }
  let b = @cat.KClass::{ p: 1, q: 4, }
  // K ≅ ℤ
  assert_eq(@cat.k_to_int(a), 2)
  assert_eq(
    @cat.k_to_int(@cat.k_add(a, b)),
    @cat.k_to_int(a) + @cat.k_to_int(b),
  )
  assert_eq(@cat.k_to_int(@cat.k_neg(a)), -@cat.k_to_int(a))
  // k_eq 是同餘（交叉條件）
  assert_true(@cat.k_eq(a, @cat.KClass::{ p: 7, q: 5, }))
  assert_false(@cat.k_eq(a, b))
  // 泛性交換圖：f(m) = c·m mod n
  let n = 5
  let c3 = 3
  // f̃([p,q]) = f(p) − f(q)：3·5 − 3·3 = 15−9 = 6 ≡ 1 (mod 5)
  assert_eq(
    @cat.k_induced(n, c3, a),
    @num.mod_pos(@num.mod_pos(c3 * 5, n) - @num.mod_pos(c3 * 3, n), n),
  )
  // 同態性（性質）：f̃(a+b) = f̃(a)+f̃(b)
  @quickcheck.check((seed : Int32) => {
    let nn = 7
    let cc = cat_rand(seed, 1, nn)
    let x = @cat.KClass::{ p: cat_rand(seed, 2, 9), q: cat_rand(seed, 3, 9), }
    let y = @cat.KClass::{ p: cat_rand(seed, 4, 9), q: cat_rand(seed, 5, 9), }
    let lhs = @cat.k_induced(nn, cc, @cat.k_add(x, y))
    let rhs = @num.mod_pos(
      @cat.k_induced(nn, cc, x) + @cat.k_induced(nn, cc, y),
      nn,
    )
    lhs == rhs
  })
}

///|
/// 定理（有限 Yoneda）：`Nat(h¹, F) ≅ F(1)` —— 計數 = |X₁|，
/// 雙射 `b ↦ (φ(b), b)` 可往返。
test "finite Yoneda on walking arrow [1]: Nat(h1, F) ≅ F(1)" {
  // 樣例：|X0|=1、|X1|=3、φ 全 0（非單非滿都可以）
  assert_eq(@cat.yoneda_nat_count(1, 3, [0, 0, 0]), 3)
  // 樣例：|X0|=2、|X1|=4、φ=[1,0,1,0]（滿非單）
  assert_eq(@cat.yoneda_nat_count(2, 4, [1, 0, 1, 0]), 4)
  // 雙射往返
  let phi = [1, 0, 1, 0]
  for b in 0..<4 {
    let pair = @cat.yoneda_fwd(4, phi, b)
    assert_eq(@cat.yoneda_bwd(2, phi, pair), b)
    // 自然性條件：a = φ(b)
    let (a, bb) = pair
    assert_eq(a, phi[bb])
  }
  // 性質：隨機 φ → 計數定理 + 雙射
  @quickcheck.check((seed : Int32) => {
    let x0 = 1 + cat_rand(seed, 1, 3) // 1..3
    let x1 = 1 + cat_rand(seed, 2, 4) // 1..4
    let phi2 : Array[Int32] = []
    for b in 0..<x1 {
      phi2.push(cat_rand(seed + 9, b * 7 + 3, x0))
    }
    let cnt = @cat.yoneda_nat_count(x0, x1, phi2)
    let mut bij = true
    for b in 0..<x1 {
      let pair = @cat.yoneda_fwd(x1, phi2, b)
      if @cat.yoneda_bwd(x0, phi2, pair) != b {
        bij = false
      }
    }
    cnt == x1 && bij
  })
}

///|
/// 通用律檢查器在群胚字典上的實例（分割群胚）：
/// 恆等/逆/結合全部成立（同塊態射）。
test "generic law checkers: assoc/unit/inv on partition groupoid" {
  let p = @cat.PartitionGroupoid::{ cls: [0, 0, 0, 1, 1], }
  let gd = p.as_groupoid()
  let c = gd.cat
  // 恆等 + 逆：全部物體與同塊態射
  for v in 0..<5 {
    assert_true(@cat.unit_ok(c, (c.id)(v)))
  }
  for x in 0..<5 {
    for y in 0..<5 {
      if p.is_iso(x, y) {
        let f = (c.compose)((c.id)(y), (x, y)) // 良定態射
        assert_true(@cat.unit_ok(c, f))
        assert_true(@cat.inv_ok(gd, f))
      }
    }
  }
  // 結合律：塊0 內四元素三態射（120 組態射選取已夠；這裡窮舉塊內元素）
  for a in 0..<3 {
    for b in 0..<3 {
      for cc in 0..<3 {
        for d in 0..<3 {
          let f = (a, b)
          let g2 = (b, cc)
          let h = (cc, d)
          assert_true(@cat.assoc_ok(c, f, g2, h))
        }
      }
    }
  }
}
