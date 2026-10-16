// Blackbox tests for the HoTT layer: assertions + property tests.
// 對應三類測試中的 斷言 ✓ 與 屬性 ✓；公理層（FunExt/UA）見 README。

///|
test "equiv id/symm/trans laws (assertions)" {
  let id : @hott.Equiv[Int32, Int32] = @hott.id_equiv()
  assert_true(
    @hott.Equiv::is_equiv_finite(
      id,
      fn(a : Int32, b : Int32) { a == b },
      fn(a : Int32, b : Int32) { a == b },
      [0, 1, 2, -1],
      [0, 1, 2, -1],
    ),
  )
  // symm∘原 = id（逐點）
  let e = @hott.Equiv::{
    fwd: fn(x : Int32) { x + 3 },
    bwd: fn(x : Int32) { x - 3 },
  }
  let es = @hott.equiv_symm(e)
  assert_true((es.fwd)((es.bwd)(7)) == 7)
  assert_true((e.bwd)((e.fwd)(7)) == 7)
  // trans
  let f = @hott.Equiv::{
    fwd: fn(x : Int32) { x * 2 },
    bwd: fn(x : Int32) { x / 2 },
  }
  let et = @hott.equiv_trans(e, f)
  assert_true((et.bwd)((et.fwd)(5)) == 5)
  // 半伴隨擡升律
  let ha = @hott.qinv_to_halfadj(e, fn(a : Int32, b : Int32) { a == b })
  assert_true((ha.eta)(41))
}

///|
test "transport and ua-beta fragment (assertions)" {
  let e = @hott.Equiv::{
    fwd: fn(x : Int32) { x + 1 },
    bwd: fn(x : Int32) { x - 1 },
  }
  let pos = fn(y : Int32) { y > 10 }
  assert_true(@hott.transport_pred(e, pos, 10)) // 10+1 > 10
  assert_true(!@hott.transport_pred(e, pos, 0))
  assert_true(@hott.ua_beta_holds(e, pos, [-5, 0, 9, 10, 100]))
}

///|
test "propositional derivers: contrapose/trans/DNE/DeMorgan/iff (assertions)" {
  let dom = [0, 1, 2, 3]
  let p = fn(x : Int32) { @num.mod_pos(x, 2) == 0 }
  let q = fn(x : Int32) { x > 1 }
  let r = fn(x : Int32) { x != 3 }
  assert_true(@hott.contrapose_holds(p, q, dom))
  assert_true(@hott.impl_trans_holds(p, q, r, dom))
  assert_true(@hott.dne_holds(q, dom))
  assert_true(@hott.de_morgan_holds(p, q, dom))
  assert_true(@hott.iff_symm_holds(p, q, dom))
}

///|
test "funext finite fragment (assertions)" {
  let dom = [0, 1, 2, 3]
  assert_true(
    @hott.funext_finite(dom, fn(x : Int32) { x * x }, fn(x : Int32) { x * x }),
  )
  assert_true(
    !@hott.funext_finite(dom, fn(x : Int32) { x }, fn(x : Int32) { x + 1 }),
  )
}

///|
test "S1 loop space: pi_1(S1) ≅ Z and groupoid laws (assertions)" {
  // 群公理（結合、單位、逆）
  assert_true(@hott.s1_groupoid_laws(2, -3, 5))
  assert_true(@hott.s1_groupoid_laws(0, 0, 0))
  // π₁ 等價律（全域於 [−3,3]）
  let pi1 = @hott.pi1_s1_equiv()
  assert_true(
    @hott.Equiv::is_equiv_finite(
      pi1,
      fn(a : Int32, b : Int32) { a == b },
      fn(a : Int32, b : Int32) { a == b },
      [-3, -2, -1, 0, 1, 2, 3],
      [-3, -2, -1, 0, 1, 2, 3],
    ),
  )
  // S¹ 非集合（1-型見證）
  assert_true(!@hott.s1_is_set())
}

///|
test "quotient HIT: path axiom and elimination checker (assertions)" {
  // 𝔽₂[x]/(x²)：x 幂零（非單位），(x) = {0, x̄} 真理想
  let alg = @finite.FinAlg::univariate_quotient(2, [0, 0, 1])
  let x = [0, 1] // e₁ = x̄
  let one = [1, 0]
  let zero = [0, 0]
  let i = alg.principal_ideal(x)
  // 路徑公理：cls(0) = cls(x) ⟺ 0 − x ∈ (x) ✓
  assert_true(@hott.quotient_path(alg, i, zero, x))
  // cls(1) ≠ cls(x)：1 − x ∉ (x)
  assert_true(!@hott.quotient_path(alg, i, one, x))
  // 消去：f = 第0座標 在 (x) 陪集上常值（(x) 元素首座標皆0）✓
  assert_true(@hott.quotient_rec_ok(alg, i, fn(v : Array[Int32]) { v[0] }))
  // f = 第1座標 不 well-defined（0 與 x̄ 同陪集但 f 不同）✗
  assert_true(!@hott.quotient_rec_ok(alg, i, fn(v : Array[Int32]) { v[1] }))
}

///|
test "truncation levels: isProp checker + UIP fragment (assertions)" {
  assert_true(@hott.is_prop_elems([[0], [0], [0]]))
  assert_true(!@hott.is_prop_elems([[0], [1]]))
  assert_true(@hott.is_prop_elems([]))
  assert_true(@hott.int_refl_unique(7))
}

///|
test "CRT equivalence as theorem (assertions)" {
  assert_true(@hott.crt_equiv_holds(6))
  assert_true(@hott.crt_equiv_holds(8))
  assert_true(@hott.crt_equiv_holds(9))
  assert_true(@hott.crt_equiv_holds(12))
  assert_true(@hott.crt_equiv_holds(30))
  // 顯式構造：x = 2 mod 3, 3 mod 4 → 11 mod 12
  let r = @hott.crt_recombine([3, 4], [2, 3])
  assert_eq(r, 11)
}

///|
test "annihilator sum law Ann(I+J) = Ann(I) ∩ Ann(J) (assertions)" {
  let alg = @finite.FinAlg::univariate_quotient(3, [2, 0, 1]) // 𝔽₃[x]/(x²+2)
  let x = [0, 1]
  let i = alg.principal_ideal(x)
  let j = alg.principal_ideal([1, 1])
  assert_true(@hott.ann_sum_law(i, j))
}

///|
test "adjunction hom-equivalences on finite sets (assertions)" {
  assert_true(@hott.curry_equiv_holds(2, 2, 2))
  assert_true(@hott.curry_equiv_holds(3, 2, 3))
  assert_true(@hott.coprod_hom_equiv_holds(2, 3, 2))
  assert_true(@hott.coprod_hom_equiv_holds(2, 2, 3))
}

///|
test "property: propositional derivers hold for all predicate pairs (quickcheck)" {
  @quickcheck.check((m : Int32) => {
    let mask1 = @num.mod_pos(m, 256)
    let mask2 = @num.mod_pos(m / 7 + 13, 256)
    let p = fn(x : Int32) { @num.mod_pos(mask1 >> x, 2) == 1 }
    let q = fn(x : Int32) { @num.mod_pos(mask2 >> x, 2) == 1 }
    let dom = [0, 1, 2, 3, 4, 5, 6, 7]
    @hott.contrapose_holds(p, q, dom) &&
    @hott.impl_trans_holds(p, q, p, dom) &&
    @hott.de_morgan_holds(p, q, dom) &&
    @hott.iff_symm_holds(p, q, dom) &&
    @hott.dne_holds(p, dom)
  })
}

///|
test "property: S1 concatenation is a homomorphism onto (Z,+) (quickcheck)" {
  @quickcheck.check((s : Int32) => {
    let p = @num.mod_pos(s, 2000) - 1000
    let q = @num.mod_pos(@num.mod_pos(s, 997) * 31 + 7, 2000) - 1000
    let r = @num.mod_pos(@num.mod_pos(s, 983) * 17 + 5, 2000) - 1000
    @hott.s1_groupoid_laws(p, q, r) &&
    @hott.s1_concat(p, q) == p + q &&
    @hott.s1_concat(@hott.s1_inv(p), p) == @hott.s1_refl()
  })
}

///|
test "property: CRT roundtrip on random n with fresh residues (quickcheck)" {
  @quickcheck.check((s : Int32) => {
    let n = 2 + @num.mod_pos(s, 62) // n ∈ [2, 64]
    if n > 64 {
      true
    } else {
      let mods = @poly.zn_crt_components(n)
      let x = @num.mod_pos(s / 3, n)
      @hott.crt_recombine(mods, @hott.crt_forward(mods, x)) == x
    }
  })
}

///|
test "property: annihilator sum law on random principal ideals (quickcheck)" {
  @quickcheck.check((s : Int32) => {
    let p = 2 + @num.mod_pos(s, 3) // 小素數域
    let alg = @finite.FinAlg::univariate_quotient(p, [0, 1, 1]) // x²+x
    let t = @num.mod_pos(s, 997)
    let a = @num.mod_pos(t * 3 + 1, p * p)
    let b = @num.mod_pos(t * 5 + 2, p * p)
    let ea : Array[Int32] = [@num.mod_pos(a, p), a / p]
    let eb : Array[Int32] = [@num.mod_pos(b, p), b / p]
    let i = alg.principal_ideal(ea)
    let j = alg.principal_ideal(eb)
    @hott.ann_sum_law(i, j)
  })
}

///|
test "impl_pred truth table and halfadj to qinv roundtrip (assertions)" {
  let dom = [0, 1, 2, 3]
  let p = fn(x : Int32) { x > 1 }
  let q = fn(x : Int32) { @num.mod_pos(x, 2) == 0 }
  for x in dom {
    assert_eq(@hott.impl_pred(p, q)(x), !p(x) || q(x))
  }
  let e = @hott.Equiv::{
    fwd: fn(x : Int32) { x + 1 },
    bwd: fn(x : Int32) { x - 1 },
  }
  let ha = @hott.qinv_to_halfadj(e, fn(a : Int32, b : Int32) { a == b })
  let e2 = @hott.halfadj_to_qinv(ha)
  assert_eq((e2.fwd)(5), 6)
  assert_eq((e2.bwd)(6), 5)
}
