// Whitebox tests for the scheme package: assertion + property tests.

///|
fn f2x2() -> @finite.FinAlg {
  // 𝔽₂[x]/(x²): local, one prime
  @finite.FinAlg::univariate_quotient(2, [0, 0, 1])
}

///|
fn f3x3() -> @finite.FinAlg {
  // 𝔽₃[x]/(x²−1) ≅ 𝔽₃ × 𝔽₃: two primes, Boolean spectrum
  @finite.FinAlg::univariate_quotient(3, [2, 0, 1])
}

///|
test "Spec poset and Zariski topology: 𝔽₂[x]/(x²)" {
  let sp = spec(f2x2())
  assert_true(sp.primes.length() == 1)
  assert_true(sp.is_le(0, 0))
  // topology: ∅ and the whole (Spec has one point)
  assert_true(sp.open_count() == 2)
  // basic opens: units → whole space, x → empty
  let full = sp.basic_open([1, 0])
  assert_true(full.length() == 1)
  let empty = sp.basic_open([0, 1])
  assert_true(empty.length() == 0)
}

///|
test "Boolean spectrum 𝔽₃×𝔽₃: 4 opens, disjoint idempotent cover" {
  let r = f3x3()
  let sp = spec(r)
  assert_true(sp.primes.length() == 2)
  // antichain of maximal ideals (Krull dim 0)
  if sp.is_le(0, 1) && sp.is_le(1, 0) {
    abort("distinct primes comparable both ways")
  }
  // all four subsets are open: ∅, {P1}, {P2}, {P1,P2}
  assert_true(sp.open_count() == 4)
  // e = 2+2x is a nontrivial idempotent: D(e) and D(1−e) split Spec
  let e = [2, 2]
  let de = sp.basic_open(e)
  assert_true(de.length() == 1)
  let one_minus_e = @linalg.vec_add(
    3,
    r.one_elem(),
    @linalg.vec_scale(3, -1, e),
  )
  let d1e = sp.basic_open(one_minus_e)
  assert_true(d1e.length() == 1)
  assert_true(de[0] != d1e[0])
  assert_true(covers_basic(r, r.one_elem(), e, one_minus_e))
}

///|
test "structure sheaf: restriction maps are ring homomorphisms" {
  let r = f3x3()
  let e = [2, 2]
  // D(e) ⊆ D(1): restriction R → R_e exists
  let t = match restriction(r, r.one_elem(), e) {
    Some(x) => x
    None => abort("expected restriction R → R_e")
  }
  let loc_full = r.localize_at_element(r.one_elem())
  let loc_e = r.localize_at_element(e)
  assert_true(t.length() == loc_full.size())
  assert_true(loc_e.size() == 3) // 𝔽₃×𝔽₃ localized at e ≅ the e-component
  // homomorphism laws on all class pairs
  for a in 0..<loc_full.size() {
    for b in 0..<loc_full.size() {
      let lhs = t[loc_full.mul_class(a, b)]
      let rhs = loc_e.mul_class(t[a], t[b])
      assert_true(lhs == rhs)
    }
  }
  // identity class → identity class
  let one_class = loc_full.embed(r.one_elem())
  assert_true(t[one_class] == loc_e.embed(r.one_elem()))
  // no map O(D(e)) → O(D(1)): D(1) ⊄ D(e)
  assert_true(restriction(r, e, r.one_elem()) is None)
}

///|
test "sheaf gluing axiom: bijection on 𝔽₃×𝔽₃ and on the local ring" {
  let r = f3x3()
  let e = [2, 2]
  let one_minus_e = @linalg.vec_add(
    3,
    r.one_elem(),
    @linalg.vec_scale(3, -1, e),
  )
  // D(1) ⊆ D(e) ∪ D(1−e), overlap = D(0) = ∅: every pair glues uniquely
  assert_true(sheaf_gluing_bijective(r, r.one_elem(), e, one_minus_e))
  // trivial cover of the whole by itself: gluing is the identity
  assert_true(
    sheaf_gluing_bijective(r, r.one_elem(), r.one_elem(), r.one_elem()),
  )
  // non-cover fails fast
  assert_false(sheaf_gluing_bijective(r, e, one_minus_e, one_minus_e))
  // local ring: cover by anything valid — D(1) ⊆ D(1) ∪ D(x)
  let r2 = f2x2()
  assert_true(sheaf_gluing_bijective(r2, r2.one_elem(), r2.one_elem(), [0, 1]))
}

///|
test "stalks: R_P are fields, product of stalk sizes = |R| (CRT)" {
  let r = f3x3()
  let sp = spec(r)
  let mut total = 1
  for p in sp.primes {
    let stalk = r.localize_at(p)
    // stalk of a finite reduced ring at a maximal ideal is a field: 𝔽₃
    assert_true(stalk.size() == 3)
    total = total * stalk.size()
  }
  assert_true(total == 9)
}

// ---------- property tests ----------

///|

///|

///|
test "property: topology sanity — ∅ and Spec open, |τ| ≤ 2^|Spec|" {
  @quickcheck.check((seed : Int32) => {
    let s = @num.mod_pos(seed, 100000)
    let r = @testutil.prop_ring(s, [2, 3])
    let sp = spec(r)
    let n = sp.primes.length()
    let cnt = sp.open_count()
    cnt >= 2 && cnt <= @num.power_int(2, n)
  })
}

///|
test "property: restriction from Spec (h = 1) is a ring homomorphism" {
  @quickcheck.check((seed : Int32) => {
    let s = @num.mod_pos(seed, 100000)
    let r = @testutil.prop_ring(s, [2, 3])
    // random f: D(f) ⊆ D(1) always holds
    let f2 : Array[Int32] = []
    for k in 0..<r.dim {
      f2.push(@testutil.det_rand(s, 50 + k) % r.p)
    }
    match restriction(r, r.one_elem(), f2) {
      None => false
      Some(t) => {
        let loc_full = r.localize_at_element(r.one_elem())
        let loc_f = r.localize_at_element(f2)
        let mut ok = t.length() == loc_full.size()
        for a in 0..<loc_full.size() {
          for b in 0..<loc_full.size() {
            let lhs = t[loc_full.mul_class(a, b)]
            let rhs = loc_f.mul_class(t[a], t[b])
            if lhs != rhs {
              ok = false
            }
          }
        }
        ok
      }
    }
  })
}

///|
test "Spec dimension and irreducible components (assertions)" {
  // 有限環 = Artin 環 ⇒ Krull 維數 0（定理：dim 0 ⟺ 所有素理想極大）
  let sp1 = spec(f2x2())
  assert_eq(sp1.dimension(), 0)
  assert_eq(sp1.irreducible_components().length(), sp1.primes.length())
  let sp2 = spec(f3x3())
  assert_eq(sp2.dimension(), 0)
  assert_eq(sp2.irreducible_components().length(), sp2.primes.length())
  // 域：單一素理想 (0)，維數 0、分支唯一
  let f4 = @finite.FinAlg::univariate_quotient(2, [1, 1, 1])
  let sp3 = spec(f4)
  assert_eq(sp3.dimension(), 0)
  assert_eq(sp3.irreducible_components().length(), 1)
  // 與理想鏈維數（krull_dim）交叉驗證
  assert_eq(sp1.dimension(), @finite.krull_dim(f2x2()))
  assert_eq(sp3.dimension(), @finite.krull_dim(f4))
}
