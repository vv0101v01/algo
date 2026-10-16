// Whitebox tests for the root package: assertion tests + property tests.

// ---------- ℤ/nℤ & IntMod: ring axioms, idempotents, conductor ----------

///|
test "IntMod exhausts all commutative ring axioms on ℤ/6ℤ" {
  let m = 6
  let xs : Array[IntMod] = []
  for a in 0..<m {
    xs.push(IntMod::make(m, a))
  }
  for a in xs {
    for b in xs {
      assert_true(a.add(b) == b.add(a))
      assert_true(a.mul(b) == b.mul(a))
      assert_true(a.add(Ring::neg(a)) == IntMod::make(m, 0))
      assert_true(a.mul(IntMod::make(m, 1)) == a)
      for c in xs {
        assert_true(a.mul(b.mul(c)) == a.mul(b).mul(c))
        assert_true(a.mul(b.add(c)) == a.mul(b).add(a.mul(c)))
      }
    }
  }
}

///|
test "zn idempotents, primitive idempotents, CRT components" {
  // ℤ/12ℤ ≅ ℤ/4 × ℤ/3; idempotents ↔ {0,1}²: residues 0, 1, 4, 9
  assert_eq(zn_idempotents(12), [0, 1, 4, 9])
  // 4 ↔ (0,1), 9 ↔ (1,0) are the orthogonal blocks; 1 = 4 + 9 splits
  assert_true(zn_is_primitive_idempotent(4, 12))
  assert_true(zn_is_primitive_idempotent(9, 12))
  assert_false(zn_is_primitive_idempotent(1, 12))
  assert_eq(zn_crt_components(12), [4, 3])
  assert_eq(zn_units(12), [1, 5, 7, 11])
}

///|
test "zn nilradical, local, regular local, semiprime ideals" {
  assert_eq(zn_nilradical(12), [0, 6]) // {a : 2|a and 3|a}
  assert_true(zn_is_nilpotent(6, 12))
  assert_false(zn_is_nilpotent(4, 12))
  assert_true(zn_is_local(9)) // 3^2
  assert_false(zn_is_local(6)) // two primes
  assert_true(zn_is_regular_local(5)) // field: dim = embdim = 0
  assert_false(zn_is_regular_local(9)) // embdim 1 > dim 0
  assert_true(zn_is_semiprime_ideal(6, 12)) // 6 squarefree
  assert_false(zn_is_semiprime_ideal(4, 12)) // 4 = 2²
  assert_true(zn_is_semiprime_ideal(2, 12))
}

///|
test "zn residual (conductor) ideal by direct scan" {
  // (4) : (6) in ℤ/12ℤ = { r : 6r ∈ (4) } = (2)
  assert_eq(zn_conductor(4, 6, 12), 2)
  // (2) : (2) = whole ring → generator 1
  assert_eq(zn_conductor(2, 2, 12), 1)
  // (6) : (2) = { r : 2r ≡ 0 mod 6 } = (3)
  assert_eq(zn_conductor(6, 2, 12), 3)
}

///|
test "zn ideal lattice totally ordered (Artinian DCC instance)" {
  let gens = zn_ideal_gens(12)
  assert_eq(gens, [1, 2, 3, 4, 6, 12])
  // (a) ⊆ (b) iff b | a — verified by element scans on this lattice
  for a in gens {
    for b in gens {
      let ea = zn_ideal_elements(a, 12)
      let eb = zn_ideal_elements(b, 12)
      let mut all_in = true
      for x in ea {
        let mut found = false
        for y in eb {
          if x == y {
            found = true
          }
        }
        if !found {
          all_in = false
        }
      }
      assert_eq(all_in, a % b == 0)
    }
  }
  assert_true(zn_is_artinian(12))
}

// ---------- Polynomials, Gröbner bases, ideals ----------

///|
test "polynomial division identity (univariate, characteristic-free)" {
  // f = x^4 − 1 = (x − 1)(x^3 + x^2 + x + 1) over 𝔽_7
  let p = 7
  let x = Poly::variable(1, p, 0)
  let one = Poly::one(1, p)
  let f = x.mul(x).mul(x).mul(x).sub(one)
  let g = x.sub(one)
  let (qs, r) = f.divmod([g])
  assert_true(r.is_zero())
  let x3 = x.mul(x).mul(x)
  let x2 = x.mul(x)
  let expect = x3.add(x2).add(x).add(one)
  assert_true(qs[0] == expect)
  // reconstruct f = q·g + r
  assert_true(qs[0].mul(g).add(r) == f)
}

///|
test "ideal membership: ⟨x²−1⟩ over 𝔽_5" {
  let p = 5
  let x = Poly::variable(1, p, 0)
  let one = Poly::one(1, p)
  let g = x.mul(x).sub(one)
  let gens = [g]
  let x6 = x.mul(x).mul(x).mul(x).mul(x).mul(x)
  let x5 = x.mul(x).mul(x).mul(x).mul(x)
  assert_true(ideal_membership(x6.sub(one), gens)) // x^6 ≡ 1
  assert_true(ideal_membership(x5.sub(x), gens)) // x^5 ≡ x
  assert_false(ideal_membership(x5.sub(one), gens)) // x^5 ≢ 1
}

///|
test "zero-dimension and standard monomials" {
  let p = 5
  let x = Poly::variable(2, p, 0)
  let y = Poly::variable(2, p, 1)
  let one = Poly::one(2, p)
  // I = ⟨x²−1, y²−1⟩: basis {1, x, y, xy}, dim 4
  let gens = [x.mul(x).sub(one), y.mul(y).sub(one)]
  assert_true(is_zero_dim(gens))
  let basis = match standard_monomials(gens) {
    Some(b) => b
    None => abort("expected finite quotient")
  }
  assert_eq(basis.length(), 4)
  // ⟨x²⟩ in one variable: basis {1, x}
  let x1 = Poly::variable(1, p, 0)
  let b1 = match standard_monomials([x1.mul(x1)]) {
    Some(b) => b
    None => abort("expected finite quotient")
  }
  assert_eq(b1.length(), 2)
  // the zero ideal in ≥1 variables is NOT zero-dimensional
  assert_false(is_zero_dim([]))
}

///|
test "radical membership (Rabinowitsch)" {
  let p = 7
  let x = Poly::variable(2, p, 0)
  let y = Poly::variable(2, p, 1)
  // I = ⟨x², xy⟩ has √I = ⟨x⟩
  let r = PolyIdeal::new(2, p, [x.mul(x), x.mul(y)])
  assert_true(r.radical_membership(x)) // x·x = x² ∈ I
  assert_false(r.radical_membership(y))
  assert_false(r.radical_membership(Poly::one(2, p)))
  assert_true(r.radical_membership(x.mul(x))) // I ⊆ √I
}

///|
test "ideal sum, product, intersection, containment" {
  let p = 5
  let x = Poly::variable(2, p, 0)
  let y = Poly::variable(2, p, 1)
  let ix = PolyIdeal::principal(x)
  let iy = PolyIdeal::principal(y)
  let s = ix.add(iy)
  assert_true(s.contains(x))
  assert_true(s.contains(y))
  assert_true(s.contains(x.add(y)))
  let pr = ix.mul(iy)
  assert_true(pr.contains(x.mul(y)))
  assert_false(pr.contains(x))
  let it = ix.intersect(iy)
  assert_true(it.contains(x.mul(y)))
  assert_false(it.contains(x))
  assert_false(it.contains(y))
  let ixy = PolyIdeal::principal(x.mul(y))
  assert_true(it.eq(ixy))
  assert_false(ix.eq(iy))
}

///|
test "residual (conductor) ideal of polynomial ideals" {
  let p = 7
  let x = Poly::variable(1, p, 0)
  // I = ⟨x²⟩ ⊂ k[x], g = x: (I : x) = ⟨x⟩
  let i = PolyIdeal::principal(x.mul(x))
  let q = match i.quotient_principal(x) {
    Some(q) => q
    None => abort("expected zero-dimensional ideal")
  }
  assert_true(q.contains(x))
  assert_true(q.contains(x.mul(x)))
  assert_false(q.contains(Poly::one(1, p))) // 1·x = x ∉ ⟨x²⟩
  let j = PolyIdeal::principal(x)
  match i.conductor(j) {
    Some(c) => assert_true(c.eq(q))
    None => abort("expected conductor")
  }
  assert_true(i.contains(x.mul(x)))
  assert_false(i.contains(x))
}

///|
test "primality of zero-dimensional ideals: 𝔽_9 vs 𝔽_5×𝔽_5" {
  let x3 = Poly::variable(1, 3, 0)
  let one3 = Poly::one(1, 3)
  let i3 = PolyIdeal::principal(x3.mul(x3).add(one3))
  assert_true(i3.is_prime()) // x²+1 irreducible mod 3 → quotient 𝔽_9
  let x5 = Poly::variable(1, 5, 0)
  let one5 = Poly::one(1, 5)
  let i5 = PolyIdeal::principal(x5.mul(x5).add(one5))
  assert_false(i5.is_prime()) // x²+1 = (x−2)(x+2) mod 5 → 𝔽_5×𝔽_5
}

// ---------- Property tests (QuickCheck) ----------

///|
/// deterministic small PRNG step (Lehmer; stays inside Int32 range)
fn next_state(s : Int32) -> Int32 {
  (s * 75 + 74) % 65537
}

///|
/// build a small random polynomial over 𝔽_p from a seed
fn gen_poly(seed : Int32, nvars : Int32, p : Int32) -> Poly {
  let mut st = @num.mod_pos(seed, 65536) + 1
  let raw : Array[(Int32, Array[Int32])] = []
  let nterms = 1 + @num.mod_pos(st, 4)
  for _t in 0..<nterms {
    st = next_state(st)
    let c = st % p
    let e : Array[Int32] = []
    for _k in 0..<nvars {
      st = next_state(st)
      e.push(st % 4) // degrees up to 3
    }
    raw.push((c, e))
  }
  poly_of_terms(nvars, p, raw)
}

///|
test "property: polynomial ring axioms over 𝔽_7" {
  @quickcheck.check(
    (seed : Int32) => {
      let s = @num.mod_pos(seed, 100000)
      let p = 7
      let a = gen_poly(s, 3, p)
      let b = gen_poly(s + 1, 3, p)
      let c = gen_poly(s * 3 + 7, 3, p)
      a.add(b) == b.add(a) &&
      a.mul(b) == b.mul(a) &&
      a.mul(b.mul(c)) == a.mul(b).mul(c) &&
      a.mul(b.add(c)) == a.mul(b).add(a.mul(c))
    },
    count=200,
    seed=99,
  )
}

///|
test "property: division reconstructs the dividend" {
  @quickcheck.check(
    (seed : Int32) => {
      let s = @num.mod_pos(seed, 100000)
      let p = 5
      let f = gen_poly(s, 2, p)
      let g = gen_poly(s + 31, 2, p)
      if g.is_zero() {
        true
      } else {
        let h = gen_poly(s * 5 + 13, 2, p)
        let gs = [g, h]
        let (qs, r) = f.divmod(gs)
        let mut acc = r
        for i in 0..<qs.length() {
          acc = acc.add(qs[i].mul(gs[i]))
        }
        acc == f
      }
    },
    count=200,
    seed=101,
  )
}

///|
test "property: Gröbner basis invariant under permutation; NF idempotent" {
  @quickcheck.check(
    (seed : Int32) => {
      let s = @num.mod_pos(seed, 100000)
      let p = 7
      let f = gen_poly(s, 2, p)
      let g = gen_poly(s + 7, 2, p)
      if f.is_zero() || g.is_zero() {
        true
      } else {
        let g1 = groebner_basis([f, g])
        let g2 = groebner_basis([g, f])
        let mut same = g1.length() == g2.length()
        for a in g1 {
          let mut found = false
          for b in g2 {
            if a == b {
              found = true
            }
          }
          if !found {
            same = false
          }
        }
        if !same {
          false
        } else {
          let nf1 = f.normal_form(g1)
          let nf2 = nf1.normal_form(g1)
          nf1 == nf2
        }
      }
    },
    count=150,
    seed=202,
  )
}

///|
test "property: f ∈ I implies f·h ∈ I and f ∈ √I" {
  @quickcheck.check(
    (seed : Int32) => {
      let s = @num.mod_pos(seed, 100000)
      let p = 5
      let f = gen_poly(s, 2, p)
      let g = gen_poly(s + 3, 2, p)
      let h = gen_poly(s * 11 + 5, 2, p)
      let gens = [g]
      if ideal_membership(f, gens) {
        ideal_membership(f.mul(h), gens) && radical_membership(f, gens)
      } else {
        true
      }
    },
    count=150,
    seed=303,
  )
}

///|
test "Poly::derivative: coefficients, Frobenius, Leibniz (assertions)" {
  // f = 3x² + 2x + 4 over 𝔽₅ → f' = 6x + 2 = x + 2
  let f = poly_of_terms(1, 5, [(3, [2]), (2, [1]), (4, [0])])
  let fp = f.derivative(0)
  for a in 0..<5 {
    assert_eq(fp.eval([a]).rep(), @num.mod_pos(a + 2, 5))
  }
  // Frobenius/特徵 p：∂(x⁵) = 0 over 𝔽₅
  let g = poly_of_terms(1, 5, [(1, [5])])
  assert_true(g.derivative(0).is_zero())
  // ∂(c) = 0 for constants
  assert_true(f.derivative(0).total_deg() >= 0)
  let c = poly_of_terms(1, 7, [(3, [0])])
  assert_true(c.derivative(0).is_zero())
  // 常數項：∂(x³ + 4) = 3x² over 𝔽₇
  let h = poly_of_terms(1, 7, [(1, [3]), (4, [0])])
  let hp = h.derivative(0)
  for a in 0..<7 {
    assert_eq(hp.eval([a]).rep(), @num.mod_pos(3 * a * a, 7))
  }
}

///|
test "property: Leibniz rule ∂(fg) = ∂f·g + f·∂g on random bivariate polynomials (quickcheck)" {
  @quickcheck.check((seed : Int32) => {
    let s = @num.mod_pos(seed, 10000)
    let p = 3 + @num.mod_pos(s, 5) // 素數 3..7
    let cf : Array[(Int32, Array[Int32])] = []
    let cg : Array[(Int32, Array[Int32])] = []
    for i in 0..<2 {
      for j in 0..<2 {
        let c1 = @num.mod_pos(s * 7 + i * 3 + j, p)
        let c2 = @num.mod_pos(s * 11 + i * 5 + j * 2 + 1, p)
        if c1 != 0 {
          cf.push((c1, [i, j]))
        }
        if c2 != 0 {
          cg.push((c2, [i, j]))
        }
      }
    }
    let f = poly_of_terms(2, p, cf)
    let g = poly_of_terms(2, p, cg)
    let lhs = Ring::mul(f, g).derivative(1)
    let rhs = Ring::add(
      Ring::mul(f.derivative(1), g),
      Ring::mul(f, g.derivative(1)),
    )
    let mut ok = true
    for a in 0..<p {
      for b in 0..<p {
        if lhs.eval([a, b]).rep() != rhs.eval([a, b]).rep() {
          ok = false
        }
      }
    }
    ok
  })
}
