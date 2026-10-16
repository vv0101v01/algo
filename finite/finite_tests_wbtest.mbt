// Whitebox tests for the finite package: assertion + property tests.
// Rings used: 𝔽₄, 𝔽₂[x]/(x²), 𝔽₃×𝔽₃, 𝔽₅[x,y]/(x²,xy,y²) (non-regular
// local), 𝔽₂⁴ (full idempotent lattice).

///|
fn alg_f4() -> FinAlg {
  // 𝔽₂[x]/(x²+x+1): the field with 4 elements
  FinAlg::univariate_quotient(2, [1, 1, 1])
}

///|
fn alg_x2() -> FinAlg {
  // 𝔽₂[x]/(x²): local ring of dual numbers
  FinAlg::univariate_quotient(2, [0, 0, 1])
}

///|
fn alg_f3x3() -> FinAlg {
  // 𝔽₃[x]/(x²−1) ≅ 𝔽₃ × 𝔽₃
  FinAlg::univariate_quotient(3, [2, 0, 1])
}

///|
fn alg_cusp() -> FinAlg {
  // 𝔽₅[x,y]/(x², xy, y²): artinian local, non-regular, embdim 2
  FinAlg::zero_dim_quotient(5, [
    @poly.poly_of_terms(2, 5, [(1, [2, 0])]),
    @poly.poly_of_terms(2, 5, [(1, [1, 1])]),
    @poly.poly_of_terms(2, 5, [(1, [0, 2])]),
  ])
}

///|
fn alg_f2four() -> FinAlg {
  // 𝔽₂[x,y]/(x²+x, y²+y) ≅ 𝔽₂ × 𝔽₂ × 𝔽₂ × 𝔽₂
  FinAlg::zero_dim_quotient(2, [
    @poly.poly_of_terms(2, 2, [(1, [2, 0]), (1, [1, 0])]),
    @poly.poly_of_terms(2, 2, [(1, [0, 2]), (1, [0, 1])]),
  ])
}

///|

///|
test "𝔽₄ is a field: all nonzero elements are units, (0) prime, regular local" {
  let f = alg_f4()
  assert_true(f.validate())
  assert_true(f.all_elements().length() == 4)
  for a in f.all_elements() {
    if @testutil.is_zero_vec(a) {
      continue
    }
    // a³ = 1 for all a ≠ 0 in 𝔽₄
    let a3 = f.mul_elem(f.mul_elem(a, a), a)
    assert_true(@linalg.vec_eq(a3, f.one_elem()))
  }
  assert_true(f.zero_ideal().is_prime())
  assert_true(prime_ideals(f).length() == 1)
  assert_true(is_local(f))
  assert_true(krull_dim(f) == 0)
  // the zero ideal is the unique maximal ideal of a field: (R, 0) regular
  assert_true(is_regular_local_at(f.zero_ideal()))
  // a field has exactly two ideals
  assert_true(enumerate_ideals(f).length() == 2)
}

///|
test "𝔽₂[x]/(x²): nilradical, ideal lattice, regular local at (x)" {
  let r = alg_x2()
  assert_true(r.validate())
  assert_true(r.all_elements().length() == 4)
  let x = [0, 1]
  // x² = 0: x nilpotent, 1+x is a unit ((1+x)² = 1)
  assert_true(is_nilpotent(r, x))
  assert_false(is_nilpotent(r, [1, 1]))
  assert_false(is_reduced(r))
  let nil = nilradical(r)
  assert_true(nil.members.length() == 2)
  assert_true(@linalg.vec_eq(nil.members[1], x))
  // Jacobson = nilradical (commutative theorem, here witnessed directly)
  assert_true(jacobson_radical(r).eq(nil))
  // ideal lattice: {0} ⊂ (x) ⊂ R
  let ids = enumerate_ideals(r)
  assert_true(ids.length() == 3)
  assert_true(longest_ideal_chain(r) == 3)
  let mx = r.principal_ideal(x)
  assert_true(mx.members.length() == 2)
  assert_true(prime_ideals(r).length() == 1)
  assert_true(prime_ideals(r)[0].eq(mx))
  assert_true(is_local(r))
  // finite ⇒ artinian ⇒ dim R_(x) = 0, while emb dim = dim m/m² = 1
  // → NOT regular (Theorem: finite regular local rings are exactly fields)
  assert_true(embedding_dim(mx) == 1)
  assert_true(local_ring_dim(mx) == 0)
  assert_false(is_regular_local_at(mx))
  // radical tower: √(0) = (x); (x) is radical; (0) is not semiprime
  assert_true(r.zero_ideal().radical().eq(mx))
  assert_true(mx.is_semiprime())
  assert_false(r.zero_ideal().is_semiprime())
  // (x)² = (x²) = 0
  assert_true(square_ideal(mx).eq(r.zero_ideal()))
  // indecomposable: only trivial idempotents → one block
  assert_true(idempotents(r).length() == 2)
  assert_true(decompose_blocks(r).length() == 1)
}

///|
test "𝔽₃×𝔽₃: idempotents, CRT blocks, zero ideal not prime" {
  let r = alg_f3x3()
  assert_true(r.validate())
  assert_true(r.all_elements().length() == 9)
  // (1+x)(1−x) = 1 − x² = 0: zero divisors ⇒ (0) not prime
  let a = [1, 1]
  let b = [1, 2]
  assert_true(@testutil.is_zero_vec(r.mul_elem(a, b)))
  assert_false(r.zero_ideal().is_prime())
  // idempotents: {0, 1, e, 1−e}
  let es = idempotents(r)
  assert_true(es.length() == 4)
  let prims = primitive_idempotents(r)
  assert_true(prims.length() == 2)
  // primitive idempotents admit no nontrivial split...
  assert_true(split_idempotent(r, prims[0]) == None)
  // ...while 1 = e + (1 − e) splits into the two orthogonal blocks
  let e = prims[0]
  match split_idempotent(r, r.one_elem()) {
    Some((p, q)) => {
      assert_true(@testutil.is_zero_vec(r.mul_elem(p, q)))
      assert_true(@linalg.vec_eq(r.add_elem(p, q), r.one_elem()))
      let is_e = @linalg.vec_eq(p, e) || @linalg.vec_eq(q, e)
      assert_true(is_e)
    }
    None => abort("expected a nontrivial split of 1")
  }
  let blocks = decompose_blocks(r)
  assert_true(blocks.length() == 2)
  assert_true(blocks[0].dim == 1 && blocks[1].dim == 1)
  // reduced commutative: nilradical = J = 0
  assert_true(is_reduced(r))
  assert_true(jacobson_radical(r).eq(r.zero_ideal()))
  // two maximal ideals, dimension 0, not local
  assert_true(prime_ideals(r).length() == 2)
  assert_true(krull_dim(r) == 0)
  assert_false(is_local(r))
  // behavioural isomorphism with the explicit product 𝔽₃×𝔽₃
  let prod = FinAlg::product(3, [1, 1])
  assert_true(prod.validate())
  assert_true(idempotents(prod).length() == 4)
  assert_true(prime_ideals(prod).length() == 2)
}

///|
test "cusp ring 𝔽₅[x,y]/(x²,xy,y²): DCC chain, annihilator, conductor, non-regular" {
  let r = alg_cusp()
  assert_true(r.validate())
  assert_true(r.dim == 3)
  // nilradical = maximal ideal (x, y): p² = 25 elements (defined early —
  // the two independent square-zero generators are also read from it)
  let nil = nilradical(r)
  assert_true(nil.members.length() == 25)
  // pick e1 = first nonzero nilpotent, e2 = first not in span(e1)
  let e1 = nil.members[1]
  assert_false(@linalg.vec_eq(e1, r.zero_elem()))
  let mut e2 = r.zero_elem()
  let mut i2 = 2
  while i2 < nil.members.length() {
    let cand = nil.members[i2]
    let mut independent = true
    for k in 0..<r.p {
      let sc = @linalg.vec_scale(r.p, k, e1)
      if @linalg.vec_eq(sc, cand) {
        independent = false
      }
    }
    if independent {
      e2 = cand
      i2 = nil.members.length() // break
    }
    i2 = i2 + 1
  }
  assert_false(@linalg.vec_eq(e2, r.zero_elem()))
  // both generators square to zero (basis order is irrelevant)
  assert_true(@testutil.is_zero_vec(r.mul_elem(e1, e1)))
  assert_true(@testutil.is_zero_vec(r.mul_elem(e2, e2)))
  assert_true(@testutil.is_zero_vec(r.mul_elem(e1, e2)))
  // nilradical = maximal ideal (x, y): p² = 25 elements
  assert_true(nil.members.length() == 25)
  assert_false(nil.contains(r.one_elem()))
  assert_false(is_reduced(r))
  assert_true(jacobson_radical(r).eq(nil))
  // exhaustive ideal lattice: {0}, 6 lines inside m, m, R → 1+6+1+1 = 9
  let ids = enumerate_ideals(r)
  assert_true(ids.length() == 9)
  // longest descending chain: R ⊃ m ⊃ line ⊃ {0} → 4 nodes
  assert_true(longest_ideal_chain(r) == 4)
  // unique prime = maximal; Krull dimension 0
  assert_true(prime_ideals(r).length() == 1)
  assert_true(prime_ideals(r)[0].eq(nil))
  assert_true(krull_dim(r) == 0)
  assert_true(is_local(r))
  // m² = 0 → embedding dim 2, but local dim 0 → NOT regular local
  assert_true(embedding_dim(nil) == 2)
  assert_true(local_ring_dim(nil) == 0)
  assert_false(is_regular_local_at(nil))
  // Ann(x) = m and conductor ((x) : (y)) = m
  let ann = annihilator(r, e1)
  assert_true(ann.members.length() == 25)
  assert_true(ann.contains(e2))
  assert_false(ann.contains(r.one_elem()))
  let ix = r.principal_ideal(e1)
  let jy = r.principal_ideal(e2)
  assert_true(ix.members.length() == 5)
  assert_true(ix.conductor(jy).eq(nil))
  // quotient dims: dim R/(x) = 2, dim R/m = 1 (both validated)
  let q1 = ix.quotient()
  assert_true(q1.validate())
  assert_true(q1.dim == 2)
  let q2 = nil.quotient()
  assert_true(q2.validate())
  assert_true(q2.dim == 1)
  assert_true(q2.all_elements().length() == 5)
  // radical tower: (x) is not radical (y ∈ √(x) since y² = 0), m is radical
  assert_false(ix.is_semiprime())
  assert_true(ix.radical().eq(nil))
  assert_true(nil.is_semiprime())
  // subalgebra F₅[x]/(x²) ⊂ R generated by {1, x}
  let span1x = @linalg.span_elements(5, [r.one_elem(), e1])
  let sub = FinAlg::subalgebra(r, span1x, r.one_elem())
  assert_true(sub.validate())
  assert_true(sub.dim == 2)
}

///|
test "𝔽₂⁴: idempotent lattice, primitive idempotents, block decomposition" {
  let r = alg_f2four()
  assert_true(r.validate())
  assert_true(r.dim == 4)
  assert_true(r.all_elements().length() == 16)
  // Boolean ring: every element idempotent
  assert_true(idempotents(r).length() == 16)
  // 𝔽₂⁴ has exactly 4 primitive idempotents (unit vectors)
  assert_true(primitive_idempotents(r).length() == 4)
  let blocks = decompose_blocks(r)
  assert_true(blocks.length() == 4)
  for b in blocks {
    assert_true(b.dim == 1)
    assert_true(b.validate())
  }
  // Spec of a product of 4 fields: 4 maximal ideals, dimension 0
  assert_true(prime_ideals(r).length() == 4)
  assert_true(krull_dim(r) == 0)
  assert_false(is_local(r))
  assert_true(is_reduced(r))
  assert_true(jacobson_radical(r).eq(r.zero_ideal()))
}

///|
test "localization: trivial at 0 ∈ S, unchanged at units, R_(x) for dual numbers" {
  let r = alg_x2() // 4 elements: {0, 1, x, 1+x}
  // S = R → the zero ring of fractions
  let l_all = r.localize(r.all_elements())
  assert_true(l_all.size() == 1)
  // S = {1} → R itself, faithfully (|𝔽₂[x]/(x²)| = 4)
  let l_triv = r.localize([r.one_elem()])
  assert_true(l_triv.size() == 4)
  // f nilpotent: S = {1, x, x²=0, …} contains 0 → collapse
  let l_x = r.localize_at_element([0, 1])
  assert_true(l_x.size() == 1)
  // S = R ∖ (x) = {1, 1+x}: localization injects: still 4 elements
  let l_p = r.localize_at(r.principal_ideal([0, 1]))
  assert_true(l_p.size() == 4)
  // ring homomorphism laws on classes
  let c0 = l_p.embed(r.zero_elem())
  let c1 = l_p.embed(r.one_elem())
  assert_true(l_p.add_class(c0, c1) == c1)
  assert_true(l_p.mul_class(c1, c1) == c1)
  let u = l_p.embed([1, 1]) // (1+x)² = 1: a unit of order 2
  assert_true(l_p.mul_class(u, u) == c1)
  // fractions with arbitrary denominators land in the image of embed
  let fx = l_p.fraction([0, 1], [1, 1]) // x/(1+x) = x·(1+x) = x + x² = ... check class arithmetic
  let ix = l_p.embed([0, 1])
  let iu = l_p.embed([1, 1])
  assert_true(l_p.mul_class(fx, iu) == ix)
  // canonical map induced by S ⊆ T: R_{1} → R_{1,1+x} is the identity on R
  let table = l_triv.map_to(l_p)
  assert_true(table.length() == 4)
  let elems = r.all_elements()
  for c in 0..<4 {
    assert_true(table[c] == l_p.embed(elems[c]))
  }
}

///|
test "quotient, generate, conductor identities on dual numbers" {
  let r = alg_x2()
  let x = [0, 1]
  // generate({1, x}) = R
  assert_true(FinIdeal::generate(r, [r.one_elem(), x]).eq(r.unit_ideal()))
  // generate({x}) = (x)
  assert_true(FinIdeal::generate(r, [x]).eq(r.principal_ideal(x)))
  // conductor special cases: (I : R) = I, (I : 0) = R, (R : J) = R
  let mx = r.principal_ideal(x)
  assert_true(mx.conductor(r.unit_ideal()).eq(mx))
  assert_true(mx.conductor(r.zero_ideal()).eq(r.unit_ideal()))
  assert_true(r.unit_ideal().conductor(mx).eq(r.unit_ideal()))
  // Ann(0) = R, Ann(R) = 0
  assert_true(annihilator(r, r.zero_elem()).eq(r.unit_ideal()))
  assert_true(annihilator_ideal(r.unit_ideal()).eq(r.zero_ideal()))
  // quotient R/(x) ≅ 𝔽₂
  let q = mx.quotient()
  assert_true(q.validate())
  assert_true(q.dim == 1)
  assert_true(q.all_elements().length() == 2)
}

// ---------- property tests ----------

///|

///|

///|

///|
test "property: random univariate quotients satisfy commutative ring axioms" {
  @quickcheck.check((seed : Int32) => {
    let s = @num.mod_pos(seed, 100000)
    let r = @testutil.prop_ring(s, [2, 3, 5])
    let a = @testutil.prop_elem(s, 1, r.p, r.dim)
    let b = @testutil.prop_elem(s, 2, r.p, r.dim)
    let c = @testutil.prop_elem(s, 3, r.p, r.dim)
    let ab_c = r.add_elem(r.add_elem(a, b), c)
    let a_bc = r.add_elem(a, r.add_elem(b, c))
    let c1 = @linalg.vec_eq(ab_c, a_bc)
    let c2 = @linalg.vec_eq(r.add_elem(a, b), r.add_elem(b, a))
    let c3 = @linalg.vec_eq(
      r.mul_elem(a, r.add_elem(b, c)),
      r.add_elem(r.mul_elem(a, b), r.mul_elem(a, c)),
    )
    let c4 = @linalg.vec_eq(
      r.mul_elem(r.mul_elem(a, b), c),
      r.mul_elem(a, r.mul_elem(b, c)),
    )
    let c5 = @linalg.vec_eq(r.mul_elem(a, b), r.mul_elem(b, a))
    let c6 = @linalg.vec_eq(r.add_elem(a, r.neg_elem(a)), r.zero_elem())
    c1 && c2 && c3 && c4 && c5 && c6
  })
}

///|
test "property: dim R/(g) = dim R − dim (g) for principal ideals" {
  @quickcheck.check((seed : Int32) => {
    let s = @num.mod_pos(seed, 100000)
    let r = @testutil.prop_ring(s, [2, 3, 5])
    let g = @testutil.prop_elem(s, 7, r.p, r.dim)
    let ideal = r.principal_ideal(g)
    if ideal.contains(r.one_elem()) {
      true // unit generator: quotient is the zero ring (not representable)
    } else {
      let q = ideal.quotient()
      let ok1 = q.validate()
      let ok2 = q.dim == r.dim - ideal_dim(ideal)
      ok1 && ok2
    }
  })
}

///|
test "property: localizing at S = R collapses to a single class" {
  @quickcheck.check((seed : Int32) => {
    let s = @num.mod_pos(seed, 100000)
    let r = @testutil.prop_ring(s, [2, 3, 5])
    // keep |R| ≤ 9 so the O(|R|²·|S|²) classing stays cheap
    if @num.power_int(r.p, r.dim) <= 9 {
      r.localize(r.all_elements()).size() == 1
    } else {
      true
    }
  })
}

///|
test "property: J(R) = Nil(R) ⊆ every prime ideal (finite commutative)" {
  @quickcheck.check((seed : Int32) => {
    let s = @num.mod_pos(seed, 100000)
    let r = @testutil.prop_ring(s, [2, 3, 5])
    let nil = nilradical(r)
    let jac = jacobson_radical(r)
    let mut ok = jac.eq(nil)
    for p_ideal in prime_ideals(r) {
      for x in nil.members {
        if !p_ideal.contains(x) {
          ok = false
        }
      }
    }
    ok
  })
}

///|
test "missed structure algorithms: socle, simple ideals, Wedderburn-Artin (assertions)" {
  // 𝔽₄：域 → 單純、半單、Wedderburn 分解為自身、socle = R
  let f4 = alg_f4()
  assert_true(is_field_alg(f4))
  assert_true(is_semisimple_ring(f4))
  assert_true(is_wedderburn_product(f4))
  assert_eq(simple_ideals(f4).length(), 1)
  assert_true(is_simple_ideal(f4.principal_ideal(f4.one_elem())))
  assert_true(!is_simple_ideal(f4.zero_ideal()))
  assert_eq(socle(f4).members.length(), 4) // Ann(0) = R
  // 𝔽₂[x]/(x²)：非域、非半單；單純理想 = (x)；socle = Ann(J) = (x)
  let x2 = alg_x2()
  assert_true(!is_field_alg(x2))
  assert_true(!is_semisimple_ring(x2))
  assert_true(!is_wedderburn_product(x2))
  let simples = simple_ideals(x2)
  assert_eq(simples.length(), 1)
  assert_eq(simples[0].members.length(), 2)
  assert_eq(socle(x2).members.length(), 2)
  // 𝔽₃×𝔽₃：半單、兩個域角 𝔽₃×𝔽₃ ≅ 𝔽₃ × 𝔽₃
  let prod = alg_f3x3()
  assert_true(is_semisimple_ring(prod))
  assert_true(is_wedderburn_product(prod))
  let fields = wedderburn_fields(prod)
  assert_eq(fields.length(), 2)
  assert_true(is_field_alg(fields[0]))
  assert_true(is_field_alg(fields[1]))
  assert_eq(fields[0].dim + fields[1].dim, prod.dim)
}
