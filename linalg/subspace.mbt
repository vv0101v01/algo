///|
/// Lexicographic comparison of coordinate vectors (`< 0`, `= 0`, `> 0`).
pub fn vec_cmp(a : Array[Int32], b : Array[Int32]) -> Int32 {
  let n = a.length()
  if n != b.length() {
    abort("vec_cmp: dimension mismatch")
  }
  for i in 0..<n {
    if a[i] != b[i] {
      return a[i].compare(b[i])
    }
  }
  0
}

///|
/// Componentwise sum in `𝔽_p^n`.
pub fn vec_add(p : Int32, a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<a.length() {
    out.push(@num.mod_pos(a[i] + b[i], p))
  }
  out
}

///|
/// Scalar multiple `c · a` in `𝔽_p^n`.
pub fn vec_scale(p : Int32, c : Int32, a : Array[Int32]) -> Array[Int32] {
  let cc = @num.mod_pos(c, p)
  let out : Array[Int32] = []
  for i in 0..<a.length() {
    out.push(@num.mul_mod(cc, a[i], p))
  }
  out
}

///|
/// Normalize, sort lexicographically and deduplicate a list of vectors.
/// After normalization the sorted list is a canonical form of the set.
pub fn elems_normalize(
  p : Int32,
  elems : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for e in elems {
    let v : Array[Int32] = []
    for x in e {
      v.push(@num.mod_pos(x, p))
    }
    out.push(v)
  }
  out.sort_by(vec_cmp)
  let dedup : Array[Array[Int32]] = []
  for v in out {
    if dedup.length() == 0 || !int_arrays_eq(dedup[dedup.length() - 1], v) {
      dedup.push(v)
    }
  }
  dedup
}

///|
/// Membership test in a canonically sorted element list (binary search).

///|
/// Equality of two single vectors.
pub fn vec_eq(a : Array[Int32], b : Array[Int32]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if a[i] != b[i] {
      return false
    }
  }
  true
}

///|
pub fn elems_contains(elems : Array[Array[Int32]], v : Array[Int32]) -> Bool {
  let mut lo = 0
  let mut hi = elems.length() - 1
  while lo <= hi {
    let mid = lo + (hi - lo) / 2
    let c = vec_cmp(elems[mid], v)
    if c == 0 {
      return true
    }
    if c < 0 {
      lo = mid + 1
    } else {
      hi = mid - 1
    }
  }
  false
}

///|
/// Equality of two normalized element lists.
pub fn elems_eq(a : Array[Array[Int32]], b : Array[Array[Int32]]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if !int_arrays_eq(a[i], b[i]) {
      return false
    }
  }
  true
}

///|
/// The `𝔽_p`-linear span of a generating set, returned as a normalized
/// element list (including `0`). Algorithm: successive line expansion,
/// `O(|gens| · p · |span|)`.
pub fn span_elements(
  p : Int32,
  gens : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let n = if gens.length() == 0 { 0 } else { gens[0].length() }
  let zero : Array[Int32] = []
  for _i in 0..<n {
    zero.push(0)
  }
  let mut cur : Array[Array[Int32]] = [zero]
  // Incremental expansion, re-normalized after every generator: without the
  // per-step dedup the working set grows like p^(#gens) (exponential blowup).
  for g in gens {
    let snapshot = cur.copy()
    for x in snapshot {
      for t in 1..<p {
        let y = vec_add(p, x, vec_scale(p, t, g))
        if !elems_contains(cur, y) {
          cur.push(y)
        }
      }
    }
    cur = elems_normalize(p, cur)
  }
  cur
}

///|
/// Close a subspace under a family of linear maps (`actions`).
/// Theorem: the result is the smallest set containing `elems` that is both an
/// `𝔽_p`-subspace and invariant under every map in `actions`.
pub fn close_under_actions(
  p : Int32,
  elems : Array[Array[Int32]],
  actions : Array[Matrix],
) -> Array[Array[Int32]] {
  let mut cur = elems_normalize(p, elems)
  let mut changed = true
  while changed {
    changed = false
    for a in actions {
      for x in cur.copy() {
        let y = a.apply(x)
        if !elems_contains(cur, y) {
          cur.push(y)
          changed = true
        }
      }
    }
    if changed {
      cur = span_elements(p, cur)
    }
  }
  cur
}

///|
/// Enumerate every vector of `𝔽_p^n` (guard: `p^n` must fit the `Int` range).
pub fn enumerate_vectors(p : Int32, n : Int32) -> Array[Array[Int32]] {
  let total = @num.power_int(p, n)
  if total > 200000 {
    abort("enumerate_vectors: p^n too large")
  }
  let out : Array[Array[Int32]] = []
  for code in 0..<total {
    let v : Array[Int32] = []
    let mut x = code
    for _i in 0..<n {
      v.push(@num.mod_pos(x, p))
      x = x / p
    }
    out.push(v)
  }
  out
}

///|
/// Enumerate all `𝔽_p`-subspaces of `𝔽_p^n` that are invariant under every
/// map in `actions` (the empty action list enumerates *all* subspaces).
/// Each subspace is returned as a normalized element list.
/// Algorithm: closure-system BFS — from every known subspace, close the span
/// of each extra vector under the action family and keep unseen results.
/// Complexity guard: intended for `n <= 4` without actions (all-subspace
/// lattices) and small `n` in general; the element universe is `p^n <= 200000`.
pub fn enumerate_closed_subspaces(
  p : Int32,
  n : Int32,
  actions : Array[Matrix],
) -> Array[Array[Array[Int32]]] {
  if p < 2 {
    abort("enumerate_closed_subspaces: prime field required")
  }
  if n == 0 {
    let only : Array[Array[Int32]] = [[]]
    return [only]
  }
  let all = enumerate_vectors(p, n)
  let zero : Array[Int32] = []
  for _i in 0..<n {
    zero.push(0)
  }
  let zero_space : Array[Array[Int32]] = [zero]
  let queue : Array[Array[Array[Int32]]] = [zero_space]
  let mut i = 0
  while i < queue.length() {
    let s = queue[i]
    for v in all {
      if elems_contains(s, v) {
        continue
      }
      let seed : Array[Array[Int32]] = []
      for x in s {
        seed.push(x)
      }
      seed.push(v)
      let t = close_under_actions(p, span_elements(p, seed), actions)
      let mut fresh = true
      for u in queue {
        if elems_eq(u, t) {
          fresh = false
          break
        }
      }
      if fresh {
        queue.push(t)
      }
    }
    i = i + 1
  }
  queue
}
