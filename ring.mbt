///|
/// The category of (associative, unital) rings as a MoonBit trait.
///
/// Definition (ring): a set `R` with `+`, `·`, `0`, `1` where `(R,+,0)` is an
/// abelian group, multiplication is associative and unital, and `·` distributes
/// over `+`. We work with *commutative* rings (`a.mul(b) == b.mul(a)`), which is
/// checked by the assertion tests for every instance in this library.
///
/// Zero-cost abstraction: trait-bound generic functions such as
/// `ring_pow[T : Ring]` are monomorphized by the compiler — static dispatch,
/// no boxing, no dictionary passing at runtime.
pub trait Ring {
  fn add(Self, Self) -> Self
  fn sub(Self, Self) -> Self
  fn mul(Self, Self) -> Self
  fn neg(Self) -> Self
  /// The additive identity. Because structured rings (`R[x]`, quotients) need
  /// ambient data (arity, modulus), the identity is derived from a sample
  /// element of the same ring — mathematically: `0_R` of the structure `R`
  /// that `self` belongs to.
  fn zero_like(Self) -> Self
  /// The multiplicative identity of the same structure.
  fn one_like(Self) -> Self
}

///|
/// Fields (every nonzero element invertible) — the coefficient context where
/// Gröbner bases and multivariate division are exact.
pub trait Field: Ring {
  /// `Some(a⁻¹)` with `a · a⁻¹ = 1`, or `None` when `a = 0`.
  fn try_inv(Self) -> Self?
}

///|
/// Generic exponentiation in any ring: `x^n` for `n >= 0` by square-and-multiply.
/// Theorem: `x^0 = 1`, `x^(a+b) = x^a · x^b` (used as a proof-by-test below).
pub fn[T : Ring] ring_pow(x : T, n : Int32) -> T {
  let mut result = x.one_like()
  let mut b = x
  let mut k = n
  while k > 0 {
    if @num.mod_pos(k, 2) == 1 {
      result = result.mul(b)
    }
    b = b.mul(b)
    k = k / 2
  }
  result
}

///|
/// Additive version: `n · x` for `n >= 0`.
pub fn[T : Ring] ring_int_mul(x : T, n : Int32) -> T {
  let mut result = x.zero_like()
  let mut k = n
  let mut b = x
  while k > 0 {
    if @num.mod_pos(k, 2) == 1 {
      result = result.add(b)
    }
    b = b.add(b)
    k = k / 2
  }
  result
}

///|
/// An element of `ℤ/mℤ` in canonical form `0 <= val < modulus`.
/// Definition: `ℤ/mℤ = ℤ / mℤ` is a commutative ring with `m >= 1`.
pub(all) struct IntMod {
  val : Int32
  modulus : Int32
} derive(Debug, Eq)

///|
/// Canonical constructor: `IntMod::make(m, a)` is `ā ∈ ℤ/mℤ`.
pub fn IntMod::make(modulus : Int32, a : Int32) -> Self {
  if modulus < 1 {
    abort("IntMod: modulus must be >= 1")
  }
  IntMod::{ val: @num.mod_pos(a, modulus), modulus, }
}

///|
/// Lift back to the representative in `[0, m)`.
pub fn IntMod::rep(self : Self) -> Int32 {
  self.val
}

///|
/// Ring instance for `ℤ/mℤ` (operations abort on modulus mismatch, i.e. the
/// morphisms we consider all live over one fixed `m`).
// 將 Ring 方法顯式掛回 IntMod（避免 implicit promotion 廢棄警告）
extend IntMod with Ring::{add, mul}

///|
extend IntMod with Field::{try_inv}

///|
pub impl Ring for IntMod with fn add(self, other) {
  if self.modulus != other.modulus {
    abort("IntMod::add: modulus mismatch")
  }
  IntMod::{
    val: @num.mod_pos(self.val + other.val, self.modulus),
    modulus: self.modulus,
  }
}

///|
pub impl Ring for IntMod with fn sub(self, other) {
  if self.modulus != other.modulus {
    abort("IntMod::sub: modulus mismatch")
  }
  IntMod::{
    val: @num.mod_pos(self.val - other.val, self.modulus),
    modulus: self.modulus,
  }
}

///|
pub impl Ring for IntMod with fn mul(self, other) {
  if self.modulus != other.modulus {
    abort("IntMod::mul: modulus mismatch")
  }
  IntMod::{
    val: @num.mul_mod(self.val, other.val, self.modulus),
    modulus: self.modulus,
  }
}

///|
pub impl Ring for IntMod with fn neg(self) {
  IntMod::{
    val: if self.val == 0 {
      0
    } else {
      self.modulus - self.val
    },
    modulus: self.modulus,
  }
}

///|
pub impl Ring for IntMod with fn zero_like(self) {
  IntMod::{ val: 0, modulus: self.modulus, }
}

///|
pub impl Ring for IntMod with fn one_like(self) {
  IntMod::{ val: @num.mod_pos(1, self.modulus), modulus: self.modulus, }
}

///|
/// `ℤ/mℤ` is a field iff `m` is prime; `try_inv` implements `a⁻¹` via the
/// extended Euclidean algorithm. Theorem: for prime `p`, every `a ≠ 0` has a
/// unique inverse in `𝔽_p`.
pub impl Field for IntMod with fn try_inv(self) {
  match @num.invmod(self.val, self.modulus) {
    Some(x) => Some(IntMod::{ val: x, modulus: self.modulus, })
    None => None
  }
}

///|
/// Fast exponentiation specialized to `ℤ/mℤ` (avoids trait dispatch in hot loops).
pub fn zn_pow(a : Int32, e : Int32, m : Int32) -> Int32 {
  @num.powmod(a, e, m)
}

///|
/// Theorem: `a` is a unit of `ℤ/nℤ` iff `gcd(a, n) = 1`.
pub fn zn_is_unit(a : Int32, n : Int32) -> Bool {
  @num.gcd(@num.mod_pos(a, n), n) == 1
}

///|
/// The multiplicative group `(ℤ/nℤ)^×` as a sorted list of residues.
pub fn zn_units(n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for a in 0..<n {
    if zn_is_unit(a, n) {
      out.push(a)
    }
  }
  out
}

///|
/// Definition (idempotent): `e² = e`. Algorithm: exhaustive scan of `ℤ/nℤ`
/// (feasible for `Int`-range moduli used here); returns sorted residues.
pub fn zn_idempotents(n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for e in 0..<n {
    if @num.mul_mod(e, e, n) == @num.mod_pos(e, n) {
      out.push(e)
    }
  }
  out
}

///|
/// Definition (primitive idempotent): an idempotent `e ≠ 0, 1` that cannot be
/// written `e = e₁ + e₂` with `e₁e₂ = 0`, both nonzero idempotents — i.e. it
/// does not split off a nontrivial block of the ring.
pub fn zn_is_primitive_idempotent(e : Int32, n : Int32) -> Bool {
  if @num.mod_pos(e, n) != @num.mul_mod(e, e, n) {
    return false
  }
  if @num.mod_pos(e, n) == 0 {
    return false // 0 is excluded by convention
  }
  let es = zn_idempotents(n)
  for a in es {
    for b in es {
      if a == 0 || b == 0 {
        continue
      }
      if @num.mod_pos(a, n) == @num.mod_pos(e, n) ||
        @num.mod_pos(b, n) == @num.mod_pos(e, n) {
        continue
      }
      if @num.mod_pos(a + b, n) == @num.mod_pos(e, n) &&
        @num.mul_mod(a, b, n) == 0 {
        return false
      }
    }
  }
  true
}

///|
/// Definition (nilpotent): `a^k = 0` in `ℤ/nℤ` for some `k >= 1`.
/// Theorem: `a` is nilpotent in `ℤ/nℤ` iff every prime divisor of `n` divides `a`.
pub fn zn_is_nilpotent(a : Int32, n : Int32) -> Bool {
  let aa = @num.mod_pos(a, n)
  if aa == 0 {
    return true
  }
  for (p, _) in @num.factor(n) {
    if @num.mod_pos(aa, p) != 0 {
      return false
    }
  }
  true
}

///|
/// The nilradical `√(0)` of `ℤ/nℤ` as a sorted residue list.
/// Theorem (commutative rings): the nilradical is an ideal, and for `ℤ/nℤ`
/// it equals `rad(n) · ℤ/nℤ` — the set of residues divisible by `rad(n)`.
pub fn zn_nilradical(n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for a in 0..<n {
    if zn_is_nilpotent(a, n) {
      out.push(a)
    }
  }
  out
}

///|
/// Definition (semiprime / radical ideal): `I` is semiprime iff `R/I` has no
/// nonzero nilpotents, equivalently `I = √I`. For `ℤ/nℤ` the ideals are `(d)`
/// with `d | n`; the theorem says `(d)` is semiprime iff `d` is squarefree.
pub fn zn_is_semiprime_ideal(d : Int32, n : Int32) -> Bool {
  if @num.mod_pos(n, d) != 0 {
    abort("zn_is_semiprime_ideal: d must divide n")
  }
  for (_p, e) in @num.factor(d) {
    if e > 1 {
      return false
    }
  }
  true
}

///|
/// Theorem (structure of `ℤ/nℤ`): `ℤ/nℤ` is Artinian (and Noetherian) for
/// every `n` — its ideals are totally ordered by divisibility of generators
/// and there are only finitely many. This always returns `true`; the honest
/// check is `zn_ideal_lattice(n)` below, from which the descending chain
/// condition is verified exhaustively by the assertion tests.
pub fn zn_is_artinian(n : Int32) -> Bool {
  n >= 1
}

///|
/// Definition (ideal of `ℤ/nℤ`): every ideal is `(d) = d·ℤ/nℤ` with `d | n`.
/// Theorem: the map d |-> (d) is an order-reversing bijection between
/// divisors of `n` and ideals; returns the generators `d | n` sorted ascending.
pub fn zn_ideal_gens(n : Int32) -> Array[Int32] {
  @num.divisors(n)
}

///|
/// Elements of the ideal `(d)` inside `ℤ/nℤ` (sorted): `{0, d, 2d, ...} mod n`.
pub fn zn_ideal_elements(d : Int32, n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut x = 0
  while x < n {
    out.push(@num.mod_pos(x, n))
    x = x + d
  }
  out
}

///|
/// Definition (residual / conductor ideal of an inclusion): for ideals
/// `I ⊆ J` of a ring `R`, the conductor is `(I : J) = { r ∈ R | r·J ⊆ I }`.
/// In `ℤ/nℤ` with `I = (a)`, `J = (b)`: `(I : J) = (lcm(a, b) mod n)`-style
/// formula `(I:J) = (a / gcd(a, b... ))` — computed directly by residues:
/// returns the generator `d` of `(I : J)`.
/// Theorem: `(I : J) = { r : r·b ≡ 0 (mod n/gcd-scaled) }` and it equals
/// `(a / gcd(a, n/b)...)` — implemented by scan, proved by tests.
pub fn zn_conductor(a : Int32, b : Int32, n : Int32) -> Int32 {
  // (a) : (b) = { r mod n : r*b ∈ (a) } — scan residues, return gcd-generator
  let mut g = n
  for r in 0..<n {
    if @num.mod_pos(@num.mul_mod(r, b, n), a) == 0 {
      g = @num.gcd(g, r)
    }
  }
  g
}

///|
/// Theorem (CRT): Z/nZ is the product of Z/p_i^{k_i}; returns the pairwise coprime
/// moduli `p_i^{k_i}` in increasing order.
pub fn zn_crt_components(n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for (p, k) in @num.factor(n) {
    out.push(@num.power_int(p, k))
  }
  out
}

///|
/// Definition (local ring): a ring with a unique maximal ideal.
/// Theorem: `ℤ/nℤ` is local iff `n = p^k` is a prime power (the unique
/// maximal ideal is `(p)`), for `n >= 2`.
pub fn zn_is_local(n : Int32) -> Bool {
  if n < 2 {
    return false
  }
  @num.factor(n).length() == 1
}

///|
/// Definition (regular local ring): a local ring `(R, m)` with
/// `dim R = dim_k(m/m²)` (embedding dimension). Krull dimension of `ℤ/nℤ`
/// is `0` (all primes `(p)` are maximal); `dim_k(m/m²) = 0` iff `n` is
/// prime. Theorem: `ℤ/nℤ` is regular local iff `n` is prime (a field),
/// consistent with `dim = embdim = 0`.
pub fn zn_is_regular_local(n : Int32) -> Bool {
  zn_is_local(n) && @num.is_prime(n)
}

///|
/// Krull dimension of `ℤ/nℤ`: longest chain of prime ideals. Every prime
/// `(p)` is maximal, so the dimension is `0` for `n >= 2`, `-1` for the
/// zero ring `n = 1` (empty spectrum convention: return 0 here for n = 1 as
/// well, documented in README).
pub fn zn_dimension(n : Int32) -> Int32 {
  if n < 2 {
    0
  } else {
    0
  }
}

///|
/// Definition (coordinates): the canonical coordinate function of `ℤ/nℤ` —
/// the residue representative of a class, `coord(a) = a mod n ∈ [0, n)`.
pub fn zn_coordinate(a : Int32, n : Int32) -> Int32 {
  @num.mod_pos(a, n)
}
