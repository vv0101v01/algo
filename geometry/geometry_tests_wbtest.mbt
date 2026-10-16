// Whitebox tests for the geometry package: assertion + property tests.

///|
fn circle_gens(p : Int32) -> Array[@poly.Poly] {
  // x² + y² − 1
  [
    @poly.poly_of_terms(2, p, [
      (1, [2, 0]),
      (1, [0, 2]),
      (@num.mod_pos(-1, p), [0, 0]),
    ]),
  ]
}

///|
fn norm2_gens(p : Int32) -> Array[@poly.Poly] {
  // x², y² (nonradical — tests the F_p-point Nullstellensatz step)
  [
    @poly.poly_of_terms(2, p, [(1, [2, 0])]),
    @poly.poly_of_terms(2, p, [(1, [0, 2])]),
  ]
}

///|
test "circle over 𝔽₃: 4 rational points, coordinate ring of dimension 4" {
  let p = 3
  let gens = circle_gens(p)
  let v = variety(gens, 100)
  // V(x²+y²−1)(𝔽₃) = {(0,1),(0,2),(1,0),(2,0)}
  let expected : Array[Array[Int32]] = [[0, 1], [0, 2], [1, 0], [2, 0]]
  assert_true(v.length() == 4)
  for i in 0..<4 {
    assert_true(@linalg.vec_eq(v[i], expected[i]))
  }
  // I(V) roundtrip
  let i_v = vanishing_ideal(v, p, 2)
  let v2 = variety(i_v.gens, 100)
  assert_true(v2.length() == 4)
  for i in 0..<4 {
    assert_true(@linalg.vec_eq(v2[i], expected[i]))
  }
  // coordinate ring: dim = |V| = 4, validated
  match coordinate_ring(v, p, 2) {
    Some(r) => {
      assert_true(r.validate())
      assert_true(r.dim == 4)
    }
    None => abort("circle coordinate ring missing")
  }
  // CRT isomorphism: eval matrix is 4×4 of full rank
  let e = eval_matrix(v, p, 2)
  assert_true(e.rows == 4 && e.cols == 4)
  assert_true(e.rank() == 4)
  assert_true(crt_iso_holds(v, p, 2))
  // the coordinate function "x" takes each point's first coordinate
  let basis = coordinate_basis(v, p, 2)
  let mut x_idx = -1
  for k in 0..<basis.length() {
    if basis[k][0] == 1 && basis[k][1] == 0 {
      x_idx = k
    }
  }
  assert_true(x_idx >= 0)
  for a in 0..<4 {
    assert_true(e.data[a][x_idx] == v[a][0])
  }
}

///|
test "affine line x = y over 𝔽₃ and 𝔽₃² as a variety" {
  let p = 3
  let line = [@poly.poly_of_terms(2, p, [(1, [1, 0]), (p - 1, [0, 1])])] // x − y
  let v = variety(line, 100)
  assert_true(v.length() == 3)
  // whole plane: 9 points; I(S) = (x³−x, y³−y) has quotient dimension 9
  let plane = affine_points(p, 2, 100)
  assert_true(plane.length() == 9)
  let ring = coordinate_ring(plane, p, 2)
  match ring {
    Some(r) => {
      assert_true(r.validate())
      assert_true(r.dim == 9)
    }
    None => abort("plane ring missing")
  }
  assert_true(crt_iso_holds(plane, p, 2))
}

///|
test "Nullstellensatz over 𝔽_p-points: I(V(x²,y²)) = (x,y)" {
  let p = 3
  let gens = norm2_gens(p)
  let v = variety(gens, 100)
  assert_true(v.length() == 1) // only the origin
  let i_v = vanishing_ideal(v, p, 2)
  // x ∈ I(V(x², y²)) although x ∉ (x², y²)
  let x_poly = @poly.poly_of_terms(2, p, [(1, [1, 0])])
  assert_true(@poly.ideal_membership(x_poly, i_v.gens))
  assert_false(@poly.ideal_membership(x_poly, gens))
  // empty variety → zero ring not representable
  let none_ring = coordinate_ring([], p, 2)
  assert_true(none_ring is None)
}

///|
test "coordinate ring is the ring of functions: eval is a ring homomorphism" {
  let p = 3
  let v = variety(circle_gens(p), 100)
  let r = match coordinate_ring(v, p, 2) {
    Some(x) => x
    None => abort("ring missing")
  }
  let e = eval_matrix(v, p, 2) // rows = points, cols = basis
  // two fixed elements of the ring (coordinate vectors over the basis)
  let a : Array[Int32] = [1, 2, 0, 1]
  let b : Array[Int32] = [0, 1, 2, 2]
  if a.length() != r.dim || b.length() != r.dim {
    abort("fixture dim mismatch")
  }
  let prod = r.mul_elem(a, b)
  // pointwise values via the eval matrix
  for k in 0..<v.length() {
    let mut va = 0
    let mut vb = 0
    let mut vp = 0
    for j in 0..<r.dim {
      va = (va + a[j] * e.data[k][j]) % p
      vb = (vb + b[j] * e.data[k][j]) % p
      vp = (vp + prod[j] * e.data[k][j]) % p
    }
    assert_true(vp == va * vb % p)
  }
}

// ---------- property tests ----------

///|

///|
test "property: random point sets — V(I(S)) = S, dim coord = |S|, CRT iso" {
  @quickcheck.check((seed : Int32) => {
    let s = @num.mod_pos(seed, 100000)
    let p = 3
    // random nonempty subset of 𝔽₃² (9 points, inclusion by bit)
    let pts : Array[Array[Int32]] = []
    for i in 0..<9 {
      if @testutil.det_rand(s, 5 + i) % 2 == 1 {
        pts.push([i % 3, i / 3])
      }
    }
    if pts.length() == 0 {
      true
    } else {
      let i_s = vanishing_ideal(pts, p, 2)
      let v = variety(i_s.gens, 100)
      // roundtrip V(I(S)) = S
      let mut ok1 = v.length() == pts.length()
      if ok1 {
        for a in pts {
          let mut found = false
          for b in v {
            if @linalg.vec_eq(a, b) {
              found = true
            }
          }
          if !found {
            ok1 = false
          }
        }
      }
      // dimension of the coordinate ring
      let ok2 = match coordinate_ring(pts, p, 2) {
        Some(r) => r.validate() && r.dim == pts.length()
        None => false
      }
      // CRT / separatedness
      let ok3 = crt_iso_holds(pts, p, 2)
      ok1 && ok2 && ok3
    }
  })
}

///|
test "jacobian smoothness: circle over F3 smooth, cusp singular at origin (assertions)" {
  // 圓 x²+y²−1 over 𝔽₃：所有點光滑（2x, 2y 不同時為零）
  let circle = circle_gens(3)
  for pt in variety(circle, 9) {
    assert_true(smooth_at(circle, pt, 1))
  }
  assert_eq(singular_points(circle, 9, 1).length(), 0)
  // 尖點 y² − x³ over 𝔽₅：原點 ∈ V 且奇異（Jac = (−3x², 2y) = (0,0)）
  let cusp_std : Array[@poly.Poly] = [
    @poly.poly_of_terms(2, 5, [(1, [0, 2]), (4, [3, 0])]),
  ]
  let origin : Array[Int32] = [0, 0]
  assert_true(!smooth_at(cusp_std, origin, 1))
  let sing = singular_points(cusp_std, 25, 1)
  assert_eq(sing.length(), 1)
  assert_eq(sing[0][0], 0)
  assert_eq(sing[0][1], 0)
  // Jac 矩陣形狀：行數 = 生成元數、列數 = 變元數
  let j = jacobian_matrix(cusp_std, origin)
  assert_eq(j.rows, 1)
  assert_eq(j.cols, 2)
  assert_eq(j.rank(), 0)
}
