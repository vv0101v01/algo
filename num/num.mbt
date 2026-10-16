///|
/// Normalize `a` into the canonical residue range `[0, m)` (requires `m > 0`).
/// Definition (canonical coordinate of `ℤ/mℤ`): `ā = a mod m` with `0 <= ā < m`.
pub fn mod_pos(a : Int32, m : Int32) -> Int32 {
  let r = a % m
  if r < 0 {
    r + m
  } else {
    r
  }
}

///|
/// Extended Euclidean algorithm.
/// Theorem (Bézout): returns `(g, x, y)` with `g >= 0` such that
/// `a * x + b * y == g == gcd(a, b)`.
pub fn egcd(a : Int32, b : Int32) -> (Int32, Int32, Int32) {
  let mut old_r = if a < 0 { -a } else { a }
  let mut r = if b < 0 { -b } else { b }
  let mut old_s = 1
  let mut s = 0
  let mut old_t = 0
  let mut t = 1
  while r != 0 {
    let q = old_r / r
    let nr = old_r - q * r
    old_r = r
    r = nr
    let ns = old_s - q * s
    old_s = s
    s = ns
    let nt = old_t - q * t
    old_t = t
    t = nt
  }
  let x = if a < 0 { -old_s } else { old_s }
  let y = if b < 0 { -old_t } else { old_t }
  (old_r, x, y)
}

///|
/// Multiplicative inverse of `a` modulo `m` (requires `m > 0`), or `None`
/// when `gcd(a, m) != 1`. Theorem: when defined, `inv * a ≡ 1 (mod m)`.

///|
/// 模乘（溢出安全）：`a·b (mod m)`，結果 ∈ [0, m)。以俄式倍乘避免
/// Int32 溢出（`(p−1)² ≥ 2³¹` 當 `p > 46340`——單次乘法會回繞）。
pub fn mul_mod(a : Int32, b : Int32, m : Int32) -> Int32 {
  if m <= 0 {
    abort("mul_mod: modulus must be positive")
  }
  let mut acc = 0
  let mut x = mod_pos(a, m)
  let mut y = mod_pos(b, m)
  while y > 0 {
    if mod_pos(y, 2) == 1 {
      acc = mod_pos(acc + x, m)
    }
    x = mod_pos(x + x, m)
    y = y / 2
  }
  acc
}

///|
pub fn invmod(a : Int32, m : Int32) -> Int32? {
  let (g, x, _) = egcd(a, m)
  if g != 1 {
    None
  } else {
    Some(mod_pos(x, m))
  }
}

///|
/// Fast exponentiation in `ℤ/mℤ`: `base^e mod m` for `e >= 0`, `m >= 1`.
/// Algorithm: square-and-multiply, `O(log e)` modular multiplications.
pub fn powmod(base : Int32, e : Int32, m : Int32) -> Int32 {
  let mut result = mod_pos(1, m)
  let mut b = mod_pos(base, m)
  let mut k = e
  while k > 0 {
    if mod_pos(k, 2) == 1 {
      result = mul_mod(result, b, m)
    }
    b = mul_mod(b, b, m)
    k = k / 2
  }
  result
}

///|
/// Deterministic Miller–Rabin primality test with `bigint` intermediates so
/// `a * a` never overflows the 32-bit `Int` range.
/// Theorem: the first 12 prime bases make the test deterministic for every
/// `n < 318665857834031151167461`, which covers the whole `Int` range.
pub fn is_prime(n : Int32) -> Bool {
  if n < 2 {
    return false
  }
  let small : Array[Int32] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
  for p in small {
    if n == p {
      return true
    }
    if mod_pos(n, p) == 0 {
      return false
    }
  }
  // write n - 1 = d * 2^s with d odd
  let mut d = n - 1
  let mut s = 0
  while mod_pos(d, 2) == 0 {
    d = d / 2
    s = s + 1
  }
  let nb = BigInt::from_int(n)
  let one = BigInt::from_int(1)
  let nm1 = nb - one
  let nd = BigInt::from_int(d)
  for a0 in small {
    let a = BigInt::from_int(a0)
    let mut x = a.pow(nd, modulus=nb)
    if x != one && x != nm1 {
      let mut composite = true
      let mut r = 1
      while r < s {
        x = x * x % nb
        if x == nm1 {
          composite = false
          break
        }
        r = r + 1
      }
      if composite {
        return false
      }
    }
  }
  true
}

///|
/// Prime factorization by trial division, sorted by prime.
/// Returns `[(p1, e1), (p2, e2), ...]` with `n = p1^e1 * p2^e2 * ...`.
/// Complexity: `O(sqrt(n))` worst case; exact for the whole `Int` range.
pub fn factor(n : Int32) -> Array[(Int32, Int32)] {
  let out : Array[(Int32, Int32)] = []
  let mut m = if n < 0 { -n } else { n }
  if m <= 1 {
    return out
  }
  for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
    if mod_pos(m, p) == 0 {
      let mut e = 0
      while mod_pos(m, p) == 0 {
        m = m / p
        e = e + 1
      }
      out.push((p, e))
    }
  }
  let mut d = 39
  while d * d <= m {
    if mod_pos(m, d) == 0 {
      let mut e = 0
      while mod_pos(m, d) == 0 {
        m = m / d
        e = e + 1
      }
      out.push((d, e))
    }
    d = d + 2
  }
  if m > 1 {
    out.push((m, 1))
  }
  out
}

///|
/// Theorem: `n > 0` has exactly `Π_i (e_i + 1)` positive divisors when
/// `n = Π_i p_i^{e_i}`. Returns them in increasing order.
pub fn divisors(n : Int32) -> Array[Int32] {
  if n <= 0 {
    return []
  }
  let fs = factor(n)
  let mut acc : Array[Int32] = [1]
  for (p, e) in fs {
    let next : Array[Int32] = []
    let mut pk = 1
    for _i in 0..<(e + 1) {
      for d in acc {
        next.push(d * pk)
      }
      pk = pk * p
    }
    acc = []
    for d in next {
      acc.push(d)
    }
  }
  acc.sort()
  acc
}

///|
/// Chinese remainder theorem for two coprime moduli: solves
/// `x ≡ a1 (mod m1)` and `x ≡ a2 (mod m2)`; returns `(x, m1 * m2)`.
/// Theorem (CRT): a solution exists iff `a1 ≡ a2 (mod gcd(m1, m2))`, and it
/// is unique modulo `lcm(m1, m2)`; here coprimality of `m1, m2` is required.
pub fn crt_pair(
  a1 : Int32,
  m1 : Int32,
  a2 : Int32,
  m2 : Int32,
) -> (Int32, Int32)? {
  let (g, s, _t) = egcd(m1, m2)
  if g != 1 {
    return None
  }
  let m = m1 * m2
  let k = mod_pos((a2 - a1) * s, m2)
  Some((mod_pos(a1 + m1 * k, m), m))
}

///|
/// Euclidean gcd via remainder steps.
pub fn gcd(a : Int32, b : Int32) -> Int32 {
  let mut x = if a < 0 { -a } else { a }
  let mut y = if b < 0 { -b } else { b }
  while y != 0 {
    let t = x % y
    x = y
    y = t
  }
  x
}

///|
/// Integer power `base^e` for `e >= 0` by square-and-multiply.
/// Used for nilpotency probes in finite rings.
pub fn power_int(base : Int32, e : Int32) -> Int32 {
  let mut result = 1
  let mut b = base
  let mut k = e
  while k > 0 {
    if k % 2 == 1 {
      result = result * b
    }
    b = b * b
    k = k / 2
  }
  result
}
