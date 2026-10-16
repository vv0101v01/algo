///|
/// A module over a finite algebra `R = FinAlg`: an `𝔽_p`-vector space
/// `M = 𝔽_p^d` together with an action of every basis element of `R`,
/// satisfying the module axioms `e_0·m = m` and
/// `e_i·(e_j·m) = (e_i e_j)·m`, i.e.
/// `action[i] ∘ action[j] = Σ_k [e_i e_j]_k · action[k]`.
pub(all) struct FinModule {
  alg : @finite.FinAlg
  dim : Int32
  action : Array[@linalg.Matrix] // action[i] = matrix of e_i acting on M
} derive(Debug)

///|
fn onehot(n : Int32, i : Int32) -> Array[Int32] {
  let v : Array[Int32] = []
  for _k in 0..<n {
    v.push(0)
  }
  v[i] = 1
  v
}

///|
/// Check the module axioms on the given structure constants.
pub fn FinModule::validate(self : Self) -> Bool {
  if self.action.length() != self.alg.dim {
    return false
  }
  let d = self.dim
  if d == 0 {
    return true
  }
  let p = self.alg.p
  // e_0 = 1 acts as the identity
  for j in 0..<d {
    for k in 0..<d {
      let want = if j == k { 1 } else { 0 }
      if @num.mod_pos(self.action[0].data[j][k], p) != want {
        return false
      }
    }
  }
  // action_i ∘ action_j = action of e_i·e_j (test on every basis vector)
  for i in 0..<self.alg.dim {
    for j in 0..<self.alg.dim {
      let prod = self.alg.mul_elem(
        onehot(self.alg.dim, i),
        onehot(self.alg.dim, j),
      )
      for v in 0..<d {
        let jv = self.action[j].apply(onehot(d, v))
        let ijv = self.action[i].apply(jv)
        let rhs : Array[Int32] = []
        for _r in 0..<d {
          rhs.push(0)
        }
        for k in 0..<self.alg.dim {
          if prod[k] != 0 {
            let akv = self.action[k].apply(onehot(d, v))
            for r in 0..<d {
              rhs[r] = @num.mod_pos(
                rhs[r] + @num.mul_mod(prod[k], akv[r], p),
                p,
              )
            }
          }
        }
        for r in 0..<d {
          let a = @num.mod_pos(ijv[r], p)
          let b = @num.mod_pos(rhs[r], p)
          if a != b {
            return false
          }
        }
      }
    }
  }
  true
}

///|
/// The zero module (dimension 0).
pub fn FinModule::zero_module(alg : @finite.FinAlg) -> FinModule {
  FinModule::{ alg, dim: 0, action: [], }
}

///|
/// The free module `R^n` (dimension `n · dim R`; block-diagonal action).
pub fn FinModule::free(alg : @finite.FinAlg, n : Int32) -> FinModule {
  if n <= 0 {
    return FinModule::zero_module(alg)
  }
  let d = n * alg.dim
  let action : Array[@linalg.Matrix] = []
  for i in 0..<alg.dim {
    let mi = @linalg.Matrix::zero(alg.p, d, d)
    for t in 0..<n {
      for a in 0..<alg.dim {
        for b in 0..<alg.dim {
          mi.data[t * alg.dim + a][t * alg.dim + b] = alg.mult[i].data[a][b]
        }
      }
    }
    action.push(mi)
  }
  FinModule::{ alg, dim: d, action, }
}

///|
/// Coordinates of `R/I`: the annihilator space `I^⊥ = {φ ∈ R* : φ|_I = 0}`
/// (dimension `dim R − dim I`) plus a linear section of the projection.
/// Returns `(phi, split)` with `phi · split = Id`.
fn quotient_coords(i : @finite.FinIdeal) -> (@linalg.Matrix, @linalg.Matrix) {
  let p = i.alg.p
  let n = i.alg.dim
  let rows = @linalg.Matrix::from_rows(p, i.members)
  let perp = rows.nullspace()
  let q = perp.length()
  let phi = @linalg.Matrix::zero(p, q, n)
  for a in 0..<q {
    for b in 0..<n {
      phi.data[a][b] = perp[a][b]
    }
  }
  let split = @linalg.Matrix::zero(p, n, q)
  for a in 0..<q {
    let e : Array[Int32] = []
    for _t in 0..<q {
      e.push(0)
    }
    e[a] = 1
    match phi.solve(e) {
      Some(x) =>
        for b in 0..<n {
          split.data[b][a] = x[b]
        }
      None => abort("quotient_coords: phi not surjective (invariant)")
    }
  }
  (phi, split)
}

///|
/// The cyclic module `R/I` with generator `1 + I`.
/// Theorem: every cyclic module arises this way — `M ≅ R/Ann(M)`.
pub fn FinModule::cyclic(i : @finite.FinIdeal) -> FinModule {
  let alg = i.alg
  let (phi, split) = quotient_coords(i)
  let q = phi.rows
  let action : Array[@linalg.Matrix] = []
  for e in 0..<alg.dim {
    // act by e: lift (split) → multiply by e in R → project (phi)
    let mid = alg.mult[e].mul(split)
    action.push(phi.mul(mid))
  }
  let m = FinModule::{ alg, dim: q, action, }
  if !m.validate() {
    abort("FinModule::cyclic: produced structure failed validation")
  }
  m
}

///|
/// Module annihilator `Ann(M) = { r ∈ R : r·M = 0 }`: the kernel of the
/// linear map `a ↦ Σ_i a_i·action[i]`, returned as a canonical element list
/// of `R` (it is an ideal — closed under the `R`-action).
pub fn FinModule::annihilator(self : Self) -> Array[Array[Int32]] {
  let p = self.alg.p
  let n = self.alg.dim
  let d = self.dim
  // system: Σ_i a_i · action[i] = 0 → (d·d) equations in n unknowns
  let rows : Array[Array[Int32]] = []
  for r in 0..<d {
    for c in 0..<d {
      let row : Array[Int32] = []
      for i in 0..<n {
        row.push(@num.mod_pos(self.action[i].data[r][c], p))
      }
      rows.push(row)
    }
  }
  let a = @linalg.Matrix::from_rows(p, rows)
  let ker = a.nullspace()
  let out : Array[Array[Int32]] = []
  for v in ker {
    out.push(v)
  }
  if out.length() == 0 {
    // trivial kernel {0}: nullspace returns an empty basis
    let zero : Array[Int32] = []
    for _i in 0..<n {
      zero.push(0)
    }
    out.push(zero)
  }
  // nullspace returns a basis — take the full span (kernel as element set)
  @linalg.span_elements(p, out)
}

///|
/// Is the given element set a submodule of `M` (its span is closed under
/// the `R`-action)?
pub fn FinModule::is_submodule(
  self : Self,
  elems : Array[Array[Int32]],
) -> Bool {
  let p = self.alg.p
  let norm = @linalg.elems_normalize(p, elems)
  let sp = @linalg.span_elements(p, elems)
  if sp.length() != norm.length() {
    return false
  }
  let closed = @linalg.close_under_actions(p, sp, self.action)
  @linalg.elems_eq(closed, sp)
}

///|
/// Enumerate all submodules of `M` (exactly the action-closed
/// `𝔽_p`-subspaces — same closure-system BFS as for ideals).
pub fn enumerate_submodules(m : FinModule) -> Array[Array[Array[Int32]]] {
  @linalg.enumerate_closed_subspaces(m.alg.p, m.dim, m.action)
}

///|
/// The quotient module `M/N` for a submodule `N`, via the projection
/// `N^⊥` (annihilator space of the subspace `N` inside `M*`).
pub fn FinModule::quotient_module(
  self : Self,
  n_elems : Array[Array[Int32]],
) -> FinModule {
  let p = self.alg.p
  let sub = @linalg.Matrix::from_rows(p, n_elems)
  let perp = sub.nullspace()
  let q = perp.length()
  let phi = @linalg.Matrix::zero(p, q, self.dim)
  for a in 0..<q {
    for b in 0..<self.dim {
      phi.data[a][b] = perp[a][b]
    }
  }
  let split = @linalg.Matrix::zero(p, self.dim, q)
  for a in 0..<q {
    let e : Array[Int32] = []
    for _t in 0..<q {
      e.push(0)
    }
    e[a] = 1
    match phi.solve(e) {
      Some(x) =>
        for b in 0..<self.dim {
          split.data[b][a] = x[b]
        }
      None => abort("quotient_module: projection not surjective")
    }
  }
  let action : Array[@linalg.Matrix] = []
  for i in 0..<self.alg.dim {
    let mid = self.action[i].mul(split)
    action.push(phi.mul(mid))
  }
  FinModule::{ alg: self.alg, dim: q, action, }
}

///|
/// Minimal `R`-generating set of `M` by greedy `R`-span growth (the span of
/// a set is its smallest containing submodule). Theorem (finite rings are
/// noetherian): this terminates with `|gens| ≤ dim_Fp M`.
pub fn FinModule::generators(self : Self) -> Array[Array[Int32]] {
  let p = self.alg.p
  let all = @linalg.enumerate_vectors(p, self.dim)
  let gens : Array[Array[Int32]] = []
  let mut cur_len = 0
  for x in all {
    let mut z = true
    for v in x {
      if v != 0 {
        z = false
      }
    }
    if z {
      continue
    }
    if cur_len == self.dim {
      break
    }
    let seed : Array[Array[Int32]] = []
    for g in gens {
      seed.push(g)
    }
    seed.push(x)
    let sp = @linalg.close_under_actions(
      p,
      @linalg.span_elements(p, seed),
      self.action,
    )
    if sp.length() > cur_len {
      gens.push(x)
      cur_len = sp.length()
    }
  }
  gens
}

///|
/// Presentation relations: for `gens = (g_1..g_s)`, every coefficient tuple
/// `(r_1..r_s) ∈ R^s` with `Σ r_j·g_j = 0` — returned as flat `𝔽_p`-vectors
/// of length `s · dim R` (a basis of the relation lattice). Together with
/// `R^s → M, e_j ↦ g_j` this is a (finite) presentation of `M`.
pub fn FinModule::relations(
  self : Self,
  gens : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let p = self.alg.p
  let n = self.alg.dim
  let s = gens.length()
  let d = self.dim
  // unknowns: coords of (r_1, ..., r_s); equations in M
  let rows : Array[Array[Int32]] = []
  for out in 0..<d {
    let row : Array[Int32] = []
    for _u in 0..<(s * n) {
      row.push(0)
    }
    for j in 0..<s {
      for i in 0..<n {
        let v = self.action[i].apply(gens[j])[out]
        row[j * n + i] = @num.mod_pos(v, p)
      }
    }
    rows.push(row)
  }
  let mat = @linalg.Matrix::from_rows(p, rows)
  mat.nullspace()
}

///|
/// Is `M` coherent? Every finitely generated module over a finite
/// (hence noetherian) ring is coherent — the check verifies the finite
/// presentation round-trip: the relation lattice of `generators(M)` maps
/// to zero and has codimension `dim M` in `R^s`.
pub fn FinModule::is_coherent(self : Self) -> Bool {
  let gens = self.generators()
  let rel = self.relations(gens)
  let p = self.alg.p
  let s = gens.length()
  // relations form the kernel of the surjection R^s → M, so
  // rank(relations) = s·dim R − dim M (exactness of the presentation)
  let total = s * self.alg.dim
  let rows = @linalg.Matrix::from_rows(p, rel)
  let rank = rows.rank()
  let expect = total - self.dim
  rank == expect
}
