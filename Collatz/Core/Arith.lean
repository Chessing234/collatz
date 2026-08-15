/-!
# Arithmetic toolkit

Background number theory used throughout the project.

This project depends on no external library, so every fact about powers,
parity, and 2-adic valuations that later files need is proved here from the
Lean core `Nat` API.

Nothing in this file mentions the Collatz map.  It is pure arithmetic.
-/

namespace Collatz
namespace Arith

/-! ## Powers of two and three -/

/-- Every power of two is positive. -/
theorem two_pow_pos (k : Nat) : 0 < 2 ^ k := Nat.two_pow_pos k

/-- Every power of three is positive. -/
theorem three_pow_pos (k : Nat) : 0 < 3 ^ k := Nat.pow_pos (by omega)

/-- Every power of two is nonzero. -/
theorem two_pow_ne_zero (k : Nat) : 2 ^ k ≠ 0 := by
  have := two_pow_pos k; omega

/-- Every power of three is nonzero. -/
theorem three_pow_ne_zero (k : Nat) : 3 ^ k ≠ 0 := by
  have := three_pow_pos k; omega

/-- Unfolding a power of two at the successor. -/
theorem two_pow_succ (k : Nat) : 2 ^ (k + 1) = 2 * 2 ^ k := by
  rw [Nat.pow_succ]; omega

/-- Unfolding a power of three at the successor. -/
theorem three_pow_succ (k : Nat) : 3 ^ (k + 1) = 3 * 3 ^ k := by
  rw [Nat.pow_succ]; omega

/-- Powers of two are monotone in the exponent. -/
theorem two_pow_le_two_pow {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by omega) h

/-- Powers of three are monotone in the exponent. -/
theorem three_pow_le_three_pow {a b : Nat} (h : a ≤ b) : 3 ^ a ≤ 3 ^ b :=
  Nat.pow_le_pow_right (by omega) h

/-- Powers of two are strictly monotone in the exponent. -/
theorem two_pow_lt_two_pow {a b : Nat} (h : a < b) : 2 ^ a < 2 ^ b :=
  Nat.pow_lt_pow_right (by omega) h

/-- Powers of three are strictly monotone in the exponent. -/
theorem three_pow_lt_three_pow {a b : Nat} (h : a < b) : 3 ^ a < 3 ^ b :=
  Nat.pow_lt_pow_right (by omega) h

/-- A power of two is at least one. -/
theorem one_le_two_pow (k : Nat) : 1 ≤ 2 ^ k := two_pow_pos k

/-- A power of three is at least one. -/
theorem one_le_three_pow (k : Nat) : 1 ≤ 3 ^ k := three_pow_pos k

/-- A positive exponent makes a power of two at least two. -/
theorem two_le_two_pow {k : Nat} (hk : 0 < k) : 2 ≤ 2 ^ k := by
  have : 2 ^ 1 ≤ 2 ^ k := two_pow_le_two_pow hk
  simpa using this

/-- A positive exponent makes a power of three at least three. -/
theorem three_le_three_pow {k : Nat} (hk : 0 < k) : 3 ≤ 3 ^ k := by
  have : 3 ^ 1 ≤ 3 ^ k := three_pow_le_three_pow hk
  simpa using this

/-- Every natural number is dominated by the corresponding power of two. -/
theorem lt_two_pow_self (n : Nat) : n < 2 ^ n := Nat.lt_two_pow_self

/-- Powers of two dominate powers of three only through the exponent, one
direction of which is this elementary bound. -/
theorem two_pow_le_three_pow (k : Nat) : 2 ^ k ≤ 3 ^ k :=
  Nat.pow_le_pow_left (by omega) k

/-- Three to the `k` is smaller than four to the `k`, stated with powers of two. -/
theorem three_pow_lt_four_pow {k : Nat} (hk : 0 < k) : 3 ^ k < 2 ^ (2 * k) := by
  have h4 : (2:Nat) ^ (2 * k) = 4 ^ k := by
    rw [Nat.pow_mul, show (2:Nat) ^ 2 = 4 from rfl]
  rw [h4]
  exact Nat.pow_lt_pow_left (by omega) (by omega)

/-- Sum of exponents splits a power of two. -/
theorem two_pow_add (a b : Nat) : 2 ^ (a + b) = 2 ^ a * 2 ^ b := Nat.pow_add 2 a b

/-- Sum of exponents splits a power of three. -/
theorem three_pow_add (a b : Nat) : 3 ^ (a + b) = 3 ^ a * 3 ^ b := Nat.pow_add 3 a b

/-! ## Parity -/

/-- The residue of a natural number modulo two is `0` or `1`. -/
theorem mod_two_eq_zero_or_one (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 :=
  Nat.mod_two_eq_zero_or_one n

/-- An even number is twice its half. -/
theorem two_mul_div_two_of_even {n : Nat} (h : n % 2 = 0) : 2 * (n / 2) = n := by
  omega

/-- An odd number is twice its half plus one. -/
theorem two_mul_div_two_of_odd {n : Nat} (h : n % 2 = 1) : 2 * (n / 2) + 1 = n := by
  omega

/-- Doubling produces an even number. -/
theorem two_mul_mod_two (n : Nat) : (2 * n) % 2 = 0 := by omega

/-- Doubling and adding one produces an odd number. -/
theorem two_mul_add_one_mod_two (n : Nat) : (2 * n + 1) % 2 = 1 := by omega

/-- Three times an odd number plus one is even. -/
theorem three_mul_add_one_even {n : Nat} (h : n % 2 = 1) : (3 * n + 1) % 2 = 0 := by
  omega

/-- Three times an even number is even. -/
theorem three_mul_even {n : Nat} (h : n % 2 = 0) : (3 * n) % 2 = 0 := by
  omega

/-- Every power of three is odd. -/
theorem three_pow_odd (k : Nat) : 3 ^ k % 2 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [three_pow_succ]
    omega

/-- A power of two with positive exponent is even. -/
theorem two_pow_even {k : Nat} (hk : 0 < k) : 2 ^ k % 2 = 0 := by
  have h : 2 ^ k = 2 * 2 ^ (k - 1) := by
    have : k - 1 + 1 = k := by omega
    rw [← this, two_pow_succ]
    simp
  omega

/-- A power of two equals one exactly when its exponent is zero. -/
theorem two_pow_eq_one_iff {k : Nat} : 2 ^ k = 1 ↔ k = 0 := by
  constructor
  · intro h
    cases k with
    | zero => rfl
    | succ m =>
      have := two_le_two_pow (Nat.succ_pos m)
      omega
  · intro h; subst h; rfl

/-- A power of three equals one exactly when its exponent is zero. -/
theorem three_pow_eq_one_iff {k : Nat} : 3 ^ k = 1 ↔ k = 0 := by
  constructor
  · intro h
    cases k with
    | zero => rfl
    | succ m =>
      have := three_le_three_pow (Nat.succ_pos m)
      omega
  · intro h; subst h; rfl

/-- A power of two never equals a power of three unless both are one. -/
theorem two_pow_ne_three_pow {a b : Nat} (h : 2 ^ a = 3 ^ b) : a = 0 ∧ b = 0 := by
  have hodd : 3 ^ b % 2 = 1 := three_pow_odd b
  have ha : a = 0 := by
    cases a with
    | zero => rfl
    | succ m =>
      have : 2 ^ (m + 1) % 2 = 0 := two_pow_even (Nat.succ_pos m)
      omega
  subst ha
  have : (3:Nat) ^ b = 1 := by omega
  exact ⟨rfl, three_pow_eq_one_iff.mp this⟩

/-! ## Divisibility -/

/-- A divisor of a positive number is at most that number. -/
theorem le_of_dvd_pos {a b : Nat} (hb : 0 < b) (h : a ∣ b) : a ≤ b :=
  Nat.le_of_dvd hb h

/-- Two divides a number exactly when its residue modulo two vanishes. -/
theorem two_dvd_iff {n : Nat} : 2 ∣ n ↔ n % 2 = 0 := by
  constructor
  · intro h; omega
  · intro h; omega

/-- A power of two divides a number exactly when the residue vanishes. -/
theorem pow_two_dvd_iff {k n : Nat} : 2 ^ k ∣ n ↔ n % 2 ^ k = 0 :=
  Nat.dvd_iff_mod_eq_zero

/-- Powers of two form a divisibility chain. -/
theorem two_pow_dvd_two_pow {a b : Nat} (h : a ≤ b) : 2 ^ a ∣ 2 ^ b :=
  Nat.pow_dvd_pow 2 h

/-- If `2 ^ (k+1)` divides `n` then so does `2 ^ k`. -/
theorem dvd_of_succ_dvd {k n : Nat} (h : 2 ^ (k + 1) ∣ n) : 2 ^ k ∣ n :=
  Nat.dvd_trans (two_pow_dvd_two_pow (by omega)) h

/-! ## Order arithmetic used by descent arguments -/

/-- Halving strictly decreases any number greater than one. -/
theorem div_two_lt {n : Nat} (hn : 1 < n) : n / 2 < n := by omega

/-- Halving weakly decreases any number. -/
theorem div_two_le (n : Nat) : n / 2 ≤ n := by omega

/-- A strict decrease followed by a weak one is a strict decrease. -/
theorem lt_of_lt_of_le' {a b c : Nat} (h1 : a < b) (h2 : b ≤ c) : a < c := by omega

/-- Multiplying both sides of a strict inequality by a positive constant. -/
theorem mul_lt_mul_of_pos_left {a b c : Nat} (h : a < b) (hc : 0 < c) : c * a < c * b := by
  exact (Nat.mul_lt_mul_left hc).mpr h

/-- A positive multiple is at least the multiplier. -/
theorem le_mul_of_pos_right {a b : Nat} (_ha : 0 < a) (hb : 0 < b) : a ≤ a * b :=
  Nat.le_mul_of_pos_right a hb

end Arith
end Collatz
