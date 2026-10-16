///|
/// A basis of `Hom_R(M, N)`: `𝔽_p`-linear maps `T : M → N` commuting with
/// the `R`-action, i.e. `T · action_M(r) = action_N(r) · T` for every
/// `r ∈ R`. The constraints are linear in the entries of `T`, so the space
/// is computed as a nullspace over `𝔽_p`.
pub fn hom_space(m : FinModule, n : FinModule) -> Array[@linalg.Matrix] {
  let p = m.alg.p
  if m.alg.dim != n.alg.dim || m.alg.p != n.alg.p {
    abort("hom_space: different base algebras")
  }
  let dm = m.dim
  let dn = n.dim
  let nvars = dm * dn
  let rows : Array[Array[Int32]] = []
  for i in 0..<m.alg.dim {
    for a in 0..<dn {
      for b in 0..<dm {
        let row : Array[Int32] = []
        for _u in 0..<nvars {
          row.push(0)
        }
        // + coeff of T[a][v] from T·act_M
        for v in 0..<dm {
          let idx = a * dm + v
          row[idx] = @num.mod_pos(row[idx] + m.action[i].data[v][b], p)
        }
        // − coeff of T[u][b] from act_N·T
        for u in 0..<dn {
          let idx = u * dm + b
          row[idx] = @num.mod_pos(row[idx] - n.action[i].data[a][u], p)
        }
        let norm : Array[Int32] = []
        for x in row {
          norm.push(@num.mod_pos(x, p))
        }
        rows.push(norm)
      }
    }
  }
  let mat = @linalg.Matrix::from_rows(p, rows)
  let ker = mat.nullspace()
  let out : Array[@linalg.Matrix] = []
  for v in ker {
    let t = @linalg.Matrix::zero(p, dn, dm)
    for a in 0..<dn {
      for b in 0..<dm {
        t.data[a][b] = v[a * dm + b]
      }
    }
    out.push(t)
  }
  out
}

///|
/// Is `M` a projective `R`-module?
/// **Dual basis lemma**: `M` is projective iff there exist `f_1..f_s ∈ M*`
/// and `m_1..m_s ∈ M` with `Σ f_i(x)·m_i = x` for all `x`. Taking `f_i`
/// and `m_i` over `𝔽_p`-bases is no loss of generality (expanding
/// `r·f` in the `Hom`-basis shows the `R`-span of rank-one maps sits
/// inside their `𝔽_p`-span). So: pick bases `f_j` of `Hom(M, R)` and
/// `m_k` of `M`, and solve the linear system
/// `Σ_{j,k} λ_{jk} · f_j(x_b)·m_k = x_b` for all basis vectors `x_b`.
/// Theorem: solvable ⇔ `M` is a direct summand of a free module.
pub fn is_projective(m : FinModule) -> Bool {
  let p = m.alg.p
  let r = FinModule::free(m.alg, 1) // R as a module over itself
  let homs = hom_space(m, r)
  let h = homs.length()
  let d = m.dim
  if d == 0 {
    return true
  }
  if h == 0 {
    return false // no nonzero maps to R — only possible for M = 0
  }
  // unknowns λ_{j,k}: h·d ; equations: d (basis x) × d (M-coords)
  let nvars = h * d
  let rows : Array[Array[Int32]] = []
  for b in 0..<d {
    for out_r in 0..<d {
      let row : Array[Int32] = []
      for _u in 0..<nvars {
        row.push(0)
      }
      for j in 0..<h {
        // f_j(x_b) = column b of T_j  (as R-coordinates)
        for k in 0..<d {
          // contribution of λ_{j,k}: f_j(x_b) · m_k evaluated at out_r
          let mut coeff = 0
          for u in 0..<m.alg.dim {
            let ru = homs[j].data[u][b]
            if ru != 0 {
              coeff = @num.mod_pos(
                coeff + @num.mul_mod(ru, m.action[u].data[out_r][k], p),
                p,
              )
            }
          }
          row[j * d + k] = @num.mod_pos(coeff, p)
        }
      }
      rows.push(row)
    }
  }
  let mat = @linalg.Matrix::from_rows(p, rows)
  // RHS = identity map on basis vectors
  let rhs : Array[Int32] = []
  for b in 0..<d {
    for out_r in 0..<d {
      rhs.push(if b == out_r { 1 } else { 0 })
    }
  }
  mat.solve(rhs) is Some(_)
}

///|
/// Image dimension of the scalar map `x ↦ e·x` for an element
/// `e = Σ e_u·basis_u` given by coordinates.
fn image_dim_of_scalar(m : FinModule, e : Array[Int32]) -> Int32 {
  let p = m.alg.p
  let d = m.dim
  let l = @linalg.Matrix::zero(p, d, d)
  for u in 0..<m.alg.dim {
    if e[u] == 0 {
      continue
    }
    for a in 0..<d {
      for b in 0..<d {
        let v = @num.mod_pos(
          l.data[a][b] + @num.mul_mod(e[u], m.action[u].data[a][b], p),
          p,
        )
        l.data[a][b] = @num.mod_pos(v, p)
      }
    }
  }
  l.rank()
}

///|
/// Is `M ≅ R^n` free? Criteria: `dim M = n·dim R`, `M` projective, and for
/// every primitive idempotent `e` the component `e·M` has dimension
/// `n · dim(eR)` (over the fields `eR` projective = free = free rank
/// determined by dimension). Theorem: over a finite commutative ring these
/// conditions are equivalent to `M` being free of rank `n`.
pub fn is_free(m : FinModule) -> Bool {
  let alg = m.alg
  if m.dim == 0 {
    return true
  }
  if @num.mod_pos(m.dim, alg.dim) != 0 {
    return false
  }
  let n = m.dim / alg.dim
  if !is_projective(m) {
    return false
  }
  for e in @finite.primitive_idempotents(alg) {
    let block = @finite.corner(alg, e)
    let want = n * block.dim
    if image_dim_of_scalar(m, e) != want {
      return false
    }
  }
  true
}

///|
/// Does the submodule given by `n_elems` have a complement inside `M`
/// (i.e. is `0 → N → M → M/N → 0` split)? Scans all submodules `L` with
/// `N ⊕ L = M` as vector spaces and `L` closed under the action.
pub fn FinModule::complement_exists(
  self : Self,
  n_elems : Array[Array[Int32]],
) -> Bool {
  let p = self.alg.p
  let n_set = @linalg.elems_normalize(p, n_elems)
  let total = @num.power_int(p, self.dim)
  if n_set.length() == 0 {
    return true
  }
  let submods = enumerate_submodules(self)
  for l in submods {
    if n_set.length() * l.length() != total {
      continue
    }
    let mut only_zero = true
    for x in l {
      if @linalg.elems_contains(n_set, x) && !all_zero_vec(x) {
        only_zero = false
      }
    }
    if only_zero {
      return true
    }
  }
  false
}

///|
fn all_zero_vec(v : Array[Int32]) -> Bool {
  for x in v {
    if x != 0 {
      return false
    }
  }
  true
}

///|
/// Is the exact sequence `0 → N → E → E/N → 0` split? (Equivalent to
/// `complement_exists` on `N ⊆ E`; provided for sequence phrasing.)
pub fn is_split_extension(e : FinModule, n_elems : Array[Array[Int32]]) -> Bool {
  e.complement_exists(n_elems)
}
