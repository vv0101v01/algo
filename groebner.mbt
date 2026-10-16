///|
/// Buchberger's algorithm: a reduced monic Gröbner basis of `I = ⟨g_1..g_s⟩`
/// over the field `𝔽_m` (requires `m` prime), for lex order `x_0 > ... > x_{n-1}`.
///
/// Theorem (Buchberger): `G` is a Gröbner basis iff every S-polynomial
/// `S(g_i, g_j)` reduces to `0` on `G`. The algorithm adds such remainders to
/// `G` until all critical pairs reduce to zero; the first Buchberger criterion
/// (coprime leading monomials ⇒ `S`-poly reduces to `0`) skips provably
/// redundant pairs. The final interreduction yields the *unique* reduced
/// monic basis, a canonical form of `I`.
pub fn groebner_basis(gens : Array[Poly]) -> Array[Poly] {
  if gens.length() == 0 {
    return []
  }
  let nvars = gens[0].nvars
  let modulus = gens[0].modulus
  if !@num.is_prime(modulus) {
    abort("groebner_basis: coefficient ring must be a prime field (m prime)")
  }
  // filter zeros and validate ambient data
  let g : Array[Poly] = []
  for p in gens {
    if p.nvars != nvars || p.modulus != modulus {
      abort("groebner_basis: ambient mismatch among generators")
    }
    if !p.is_zero() {
      g.push(p)
    }
  }
  if g.length() == 0 {
    return []
  }
  // critical pair queue
  let pairs : Array[(Int32, Int32)] = []
  for i in 0..<g.length() {
    for j in (i + 1)..<g.length() {
      pairs.push((i, j))
    }
  }
  let mut steps = 0
  let mut pi = 0
  while pi < pairs.length() {
    steps = steps + 1
    if steps > 50000 {
      abort("groebner_basis: pair limit exceeded")
    }
    let (i, j) = pairs[pi]
    pi = pi + 1
    if i >= g.length() || j >= g.length() {
      continue
    }
    let (li, lj) = (g[i].lm(), g[j].lm())
    let (ei, ej) = (
      match li {
        Some(e) => e
        None => []
      },
      match lj {
        Some(e) => e
        None => []
      },
    )
    // first criterion: coprime leading monomials — no S-pair needed
    let mut coprime = true
    for k in 0..<nvars {
      if ei[k] != 0 && ej[k] != 0 {
        coprime = false
      }
    }
    if coprime {
      continue
    }
    let s = spoly(g[i], g[j])
    let r = s.normal_form(g)
    if !r.is_zero() {
      g.push(r)
      for k in 0..<(g.length() - 1) {
        pairs.push((k, g.length() - 1))
      }
    }
  }
  interreduce(g)
}

///|
/// Buchberger's S-polynomial:
/// `S(f, g) = (x^lcm / lm(f))·f/lc(f) − (x^lcm / lm(g))·g/lc(g)`.
/// Requires invertible leading coefficients (prime modulus — checked by
/// `groebner_basis` before any call).
pub fn spoly(f : Poly, g : Poly) -> Poly {
  let (ef, eg) = (
    match f.lm() {
      Some(e) => e
      None => return f.zero_like()
    },
    match g.lm() {
      Some(e) => e
      None => return f.zero_like()
    },
  )
  let finv = match f.lc().try_inv() {
    Some(x) => x
    None => abort("spoly: leading coefficient not invertible")
  }
  let ginv = match g.lc().try_inv() {
    Some(x) => x
    None => abort("spoly: leading coefficient not invertible")
  }
  let l = exp_lcm(ef, eg)
  let df : Array[Int32] = []
  let dg : Array[Int32] = []
  for k in 0..<f.nvars {
    df.push(l[k] - ef[k])
    dg.push(l[k] - eg[k])
  }
  let tf = f.mul_monom(finv.val, df)
  let tg = g.mul_monom(ginv.val, dg)
  tf.sub(tg)
}

///|
/// Interreduction to the reduced monic Gröbner basis: every generator is
/// monic, no leading term divides another, and each polynomial is normal
/// w.r.t. the rest. Output is sorted by descending lex order of leading terms.
fn interreduce(gs : Array[Poly]) -> Array[Poly] {
  if gs.length() == 0 {
    return []
  }
  let modulus = gs[0].modulus
  let mut out : Array[Poly] = []
  for p in gs {
    out.push(p)
  }
  let mut changed = true
  let mut passes = 0
  while changed {
    changed = false
    passes = passes + 1
    if passes > 200 {
      abort("interreduce: fixed point not reached")
    }
    let mut i = 0
    while i < out.length() {
      let others : Array[Poly] = []
      for j in 0..<out.length() {
        if j != i {
          others.push(out[j])
        }
      }
      let r = out[i].normal_form(others)
      if r.is_zero() {
        // generator was redundant
        let nxt : Array[Poly] = []
        for j in 0..<out.length() {
          if j != i {
            nxt.push(out[j])
          }
        }
        out = nxt
        changed = true
      } else {
        // make monic
        let linv = match r.lc().try_inv() {
          Some(x) => x
          None => abort("interreduce: non-invertible leading coefficient")
        }
        let raw : Array[(Int32, Array[Int32])] = []
        for t in r.terms {
          raw.push((@num.mul_mod(t.coeff.val, linv.val, modulus), t.exp))
        }
        let m = poly_of_terms(r.nvars, modulus, raw)
        if m != out[i] {
          out[i] = m
          changed = true
        }
        i = i + 1
      }
    }
  }
  out.sort_by(fn(a, b) {
    let (ea, eb) = (
      match a.lm() {
        Some(e) => e
        None => []
      },
      match b.lm() {
        Some(e) => e
        None => []
      },
    )
    lex_cmp(eb, ea) // descending: leading monomial first
  })
  out
}

///|
/// Ideal membership: `f ∈ ⟨gens⟩` iff the normal form of `f` on the reduced
/// Gröbner basis is zero (Theorem: correct for *any* Gröbner basis).
pub fn ideal_membership(f : Poly, gens : Array[Poly]) -> Bool {
  if gens.length() == 0 {
    return f.is_zero()
  }
  if f.nvars != gens[0].nvars || f.modulus != gens[0].modulus {
    abort("ideal_membership: ambient mismatch")
  }
  let g = groebner_basis(gens)
  f.normal_form(g).is_zero()
}

///|
/// Is `I` zero-dimensional (finite quotient `𝔽_p[x]/I`)? Criterion: the
/// reduced Gröbner basis contains a pure power `x_k^{a_k}` for every variable.
pub fn is_zero_dim(gens : Array[Poly]) -> Bool {
  match standard_monomials(gens) {
    Some(_) => true
    None => false
  }
}

///|
/// Standard monomials of `I` (monomials not divisible by any `lm(g)`): a
/// `𝔽_p`-basis of the quotient ring `k[x]/I`, returned in descending lex
/// order, or `None` when the quotient is infinite-dimensional.
/// Theorem (0-dimensional case): `dim_k k[x]/I = Π_k a_k` where `x_k^{a_k}`
/// are the pure powers in the basis.
pub fn standard_monomials(gens : Array[Poly]) -> Array[Array[Int32]]? {
  if gens.length() == 0 {
    return None // the zero ideal in ≥1 variables has infinite quotient
  }
  let nvars = gens[0].nvars
  let g = groebner_basis(gens)
  if g.length() == 0 {
    return None
  }
  // pure power bound per variable
  let bounds : Array[Int32] = []
  for _k in 0..<nvars {
    bounds.push(0)
  }
  for p in g {
    let e = match p.lm() {
      Some(e) => e
      None => continue
    }
    let mut nonzero = -1
    let mut pure = true
    for k in 0..<nvars {
      if e[k] != 0 {
        if nonzero != -1 {
          pure = false
        }
        nonzero = k
      }
    }
    if pure && nonzero != -1 {
      if bounds[nonzero] == 0 || e[nonzero] < bounds[nonzero] {
        if bounds[nonzero] == 0 {
          bounds[nonzero] = e[nonzero]
        }
      }
    }
  }
  // quotient finite iff every variable got a pure-power bound
  let mut total = 1
  for k in 0..<nvars {
    if bounds[k] == 0 {
      return None
    }
    total = total * bounds[k]
    if total > 100000 {
      abort("standard_monomials: quotient too large")
    }
  }
  // enumerate multi-indices 0 <= e_k < bounds[k], then keep only those
  // NOT divisible by any leading monomial of the (reduced) basis —
  // the box from pure-power bounds is a superset of the standard monomials.
  let basis : Array[Array[Int32]] = []
  for code in 0..<total {
    let e : Array[Int32] = []
    let mut x = code
    for k in 0..<nvars {
      e.push(@num.mod_pos(x, bounds[k]))
      x = x / bounds[k]
    }
    let mut ok = true
    for p in g {
      match p.lm() {
        Some(l) => {
          let mut divides = true
          for k in 0..<nvars {
            if e[k] < l[k] {
              divides = false
            }
          }
          if divides {
            ok = false
          }
        }
        None => ()
      }
    }
    if ok {
      basis.push(e)
    }
  }
  basis.sort_by(fn(a, b) { lex_cmp(b, a) }) // descending lex
  Some(basis)
}

///|
/// Radical membership via the Rabinowitsch trick:
/// `f ∈ √I ⇔ 1 ∈ ⟨I, 1 − y·f⟩ ⊂ 𝔽_p[y, x_0..x_{n-1}]`
/// (Theorem: `√I` is the set of elements vanishing on `V(I)`; adjoining
/// `y` with `y·f = 1` asks exactly whether `f` vanishes nowhere on `V(I)`).
pub fn radical_membership(f : Poly, gens : Array[Poly]) -> Bool {
  if gens.length() == 0 {
    return f.is_zero()
  }
  let nvars = f.nvars
  let modulus = f.modulus
  if f.modulus != gens[0].modulus || f.nvars != gens[0].nvars {
    abort("radical_membership: ambient mismatch")
  }
  // shift to nvars+1 variables with y = x_0 (new, dominant)
  let big = nvars + 1
  let lifted : Array[Poly] = []
  for g in gens {
    let raw : Array[(Int32, Array[Int32])] = []
    for t in g.terms {
      let e : Array[Int32] = [0]
      for x in t.exp {
        e.push(x)
      }
      raw.push((t.coeff.val, e))
    }
    lifted.push(poly_of_terms(big, modulus, raw))
  }
  // j = 1 - y*f
  let jraw : Array[(Int32, Array[Int32])] = [(1, zero_exp(big))]
  for t in f.terms {
    let e : Array[Int32] = [1]
    for x in t.exp {
      e.push(x)
    }
    jraw.push((-t.coeff.val, e))
  }
  lifted.push(poly_of_terms(big, modulus, jraw))
  ideal_membership(Poly::one(big, modulus), lifted)
}
