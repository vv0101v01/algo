// Blackbox tests: assertion tests + QuickCheck property tests for `num`.

///|
test "egcd bezout identity (assertions)" {
  let (g, x, y) = @num.egcd(240, 46)
  assert_eq(g, 2)
  assert_eq(240 * x + 46 * y, g)
  let (g2, x2, y2) = @num.egcd(-240, 46)
  assert_eq(g2, 2)
  assert_eq(-240 * x2 + 46 * y2, g2)
  let (g3, _, _) = @num.egcd(0, 0)
  assert_eq(g3, 0)
}

///|
test "invmod and powmod (assertions)" {
  assert_eq(@num.invmod(3, 7), Some(5))
  assert_eq(@num.invmod(2, 6), None)
  assert_eq(@num.powmod(2, 10, 1000), 24)
  assert_eq(@num.powmod(5, 0, 7), 1)
  // Fermat: a^(p-1) ≡ 1 (mod p) for p prime, a not divisible by p
  assert_eq(@num.powmod(3, 12, 13), 1)
}

///|
test "factor and divisors (assertions)" {
  let f = @num.factor(360) // 360 = 2^3 * 3^2 * 5
  assert_eq(f.length(), 3)
  assert_eq(f[0], (2, 3))
  assert_eq(f[1], (3, 2))
  assert_eq(f[2], (5, 1))
  let d = @num.divisors(36)
  debug_inspect(d, content="[1, 2, 3, 4, 6, 9, 12, 18, 36]")
  assert_eq(@num.divisors(36).length(), 9) // theorem: (3+1)(2+1) = 12? 36=2^2*3^2 -> 9
}

///|
test "crt (assertions)" {
  match @num.crt_pair(2, 3, 3, 5) {
    Some((x, m)) => {
      assert_eq(m, 15)
      assert_eq(x % 3, 2)
      assert_eq(x % 5, 3)
    }
    None => abort("crt should succeed for coprime moduli")
  }
  assert_eq(@num.crt_pair(1, 4, 2, 6), None) // gcd(4,6) = 2, inconsistent? 1 vs 2 mod 2 differs
}

///|
test "property: egcd Bézout on bounded inputs" {
  @quickcheck.check(
    (s : Int32) => {
      let a = s % 60001 - 30000
      let b = s / 3 % 60001 - 30000
      let (g, x, y) = @num.egcd(a, b)
      g >= 0 && a * x + b * y == g && g == @num.gcd(a, b)
    },
    count=300,
    seed=42,
  )
}

///|
test "property: powmod agrees with naive repeated multiplication" {
  @quickcheck.check(
    (s : Int32) => {
      let a = @num.mod_pos(s, 97) - 48
      let e = @num.mod_pos(s / 7, 13)
      let m = @num.mod_pos(s, 41) + 2 // m in [2, 42]
      let b = @num.mod_pos(a, m)
      let mut naive = 1 % m
      let mut i = 0
      while i < e {
        naive = naive * b % m
        i = i + 1
      }
      @num.mod_pos(naive, m) == @num.powmod(a, e, m)
    },
    count=300,
    seed=7,
  )
}

///|
test "property: factor reconstructs n and is_prime matches trial division" {
  @quickcheck.check(
    (s : Int32) => {
      let n = @num.mod_pos(s, 100000) + 2 // n >= 2
      let fs = @num.factor(n)
      let mut prod = 1
      let mut primes_ok = true
      for (p, e) in fs {
        prod = prod * @num.power_int(p, e)
        if !@num.is_prime(p) {
          primes_ok = false
        }
      }
      let mut trial = true
      let mut d = 2
      while d * d <= n {
        if n % d == 0 {
          trial = false
          break
        }
        d = d + 1
      }
      prod == n && primes_ok && @num.is_prime(n) == trial
    },
    count=200,
    seed=11,
  )
}

///|
test "property: divisors count equals brute force" {
  @quickcheck.check(
    (s : Int32) => {
      let n = @num.mod_pos(s, 3000) + 1
      let mut cnt = 0
      let mut d = 1
      while d <= n {
        if n % d == 0 {
          cnt = cnt + 1
        }
        d = d + 1
      }
      @num.divisors(n).length() == cnt
    },
    count=150,
    seed=5,
  )
}
