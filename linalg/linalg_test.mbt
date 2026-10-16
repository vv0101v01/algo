// Blackbox tests: assertion tests + QuickCheck property tests for `linalg`.

///|
test "rref and rank (assertions)" {
  let a = @linalg.Matrix::from_rows(5, [
    [1, 2, 3],
    [2, 4, 6], // second row = 2 × first
    [0, 1, 1],
  ])
  assert_eq(a.rank(), 2)
  let (r, pivots) = a.rref()
  assert_eq(pivots, [0, 1])
  // fully reduced: pivot rows are unit vectors
  assert_eq(r.get(0, 0), 1)
  assert_eq(r.get(0, 1), 0)
  assert_eq(r.get(1, 1), 1)
  assert_eq(r.get(1, 2), 1)
}

///|
test "nullspace theorem: A·x = 0 for every basis vector" {
  let a = @linalg.Matrix::from_rows(3, [[1, 1, 1], [1, 2, 0]])
  let ns = a.nullspace()
  // dim ker = cols - rank = 3 - 2 = 1
  assert_eq(ns.length(), 1)
  for v in ns {
    let w = a.apply(v)
    for x in w {
      assert_eq(x, 0)
    }
  }
}

///|
test "solve: consistent and inconsistent systems" {
  let a = @linalg.Matrix::from_rows(7, [[1, 2], [3, 4]])
  match a.solve([5, 11]) {
    Some(x) => {
      // x = (1, 2): 1 + 4 = 5, 3 + 8 = 11
      assert_eq(x[0], 1)
      assert_eq(x[1], 2)
    }
    None => abort("system is consistent")
  }
  // inconsistent over any field: second row = 2 × first, but rhs breaks that
  let dep = @linalg.Matrix::from_rows(7, [[1, 2], [2, 4]])
  match dep.solve([1, 3]) {
    Some(_) => abort("should be inconsistent")
    None => ()
  }
}

///|
test "rowspace containment" {
  let a = @linalg.Matrix::from_rows(5, [[1, 0], [0, 1]])
  let b = @linalg.Matrix::from_rows(5, [[1, 1], [2, 2]])
  assert_true(a.rowspace_contains(b))
  assert_false(b.rowspace_contains(a))
}

///|
test "subspace lattice of 𝔽_2^2 and 𝔽_3^2" {
  let act : Array[@linalg.Matrix] = []
  let s22 = @linalg.enumerate_closed_subspaces(2, 2, act)
  // theorem: F_2^2 has 1 + 3 + 1 = 5 subspaces
  assert_eq(s22.length(), 5)
  let s32 = @linalg.enumerate_closed_subspaces(3, 2, act)
  // theorem: F_3^2 has 1 + 4 + 1 = 6 subspaces
  assert_eq(s32.length(), 6)
  let s11 = @linalg.enumerate_closed_subspaces(2, 1, act)
  assert_eq(s11.length(), 2) // {0} and the line
}

///|
test "span and normalization" {
  let g1 = [1, 0]
  let g2 = [0, 1]
  let sp = @linalg.span_elements(3, [g1, g2])
  assert_eq(sp.length(), 9) // whole F_3^2
  let sp2 = @linalg.span_elements(3, [[1, 1]])
  assert_eq(sp2.length(), 3) // a line: {0, (1,1), (2,2)}
}

///|
test "property: rref is idempotent and nullspace is killed" {
  @quickcheck.check(
    (seed : Int32) => {
      let mut st = @num.mod_pos(seed, 65537) + 1
      let p = [2, 3, 5, 7][@num.mod_pos(seed, 4)]
      let rows = @num.mod_pos(seed / 2, 3) + 1
      let cols = @num.mod_pos(seed / 5, 3) + 1
      let data : Array[Array[Int32]] = []
      for _i in 0..<rows {
        let row : Array[Int32] = []
        for _j in 0..<cols {
          st = (st * 75 + 74) % 65537
          row.push(st % p)
        }
        data.push(row)
      }
      let a = @linalg.Matrix::from_rows(p, data)
      let (r1, pv1) = a.rref()
      let (r2, pv2) = r1.rref()
      let mut ok = @linalg.int_arrays_eq(pv1, pv2)
      for i in 0..<r1.rows {
        for j in 0..<r1.cols {
          if r1.get(i, j) != r2.get(i, j) {
            ok = false
          }
        }
      }
      // A annihilates its nullspace
      for v in a.nullspace() {
        for x in a.apply(v) {
          if x != 0 {
            ok = false
          }
        }
      }
      // rank-nullity
      let nullity = a.nullspace().length()
      ok && a.rank() + nullity == cols
    },
    count=200,
    seed=1,
  )
}

///|
test "property: solve reconstructs b whenever a solution exists" {
  @quickcheck.check(
    (seed : Int32) => {
      let mut st = @num.mod_pos(seed, 65537) + 1
      let p = [2, 3, 5][@num.mod_pos(seed / 3, 3)]
      let rows = 2
      let cols = 2
      let data : Array[Array[Int32]] = []
      for _i in 0..<rows {
        let row : Array[Int32] = []
        for _j in 0..<cols {
          st = (st * 75 + 74) % 65537
          row.push(st % p)
        }
        data.push(row)
      }
      st = (st * 75 + 74) % 65537
      let b0 = st % p
      st = (st * 75 + 74) % 65537
      let b1 = st % p
      let a = @linalg.Matrix::from_rows(p, data)
      match a.solve([b0, b1]) {
        None => true
        Some(x) => {
          let y = a.apply(x)
          y[0] == b0 && y[1] == b1
        }
      }
    },
    count=300,
    seed=2,
  )
}
