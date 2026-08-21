import Collatz.Strategy.GapOne

/-!
# The prime factorisation of the gap

The cycle criterion (`CycleCriterion`, `CycleAccumulator.cycle_gap_dvd`) says a
cycle is exactly a word whose gap `G = 2 ^ L − 3 ^ a` divides its accumulator
`C`.  This file asks the reverse-engineering question: **what does an integer
have to look like in order to be a gap?**  Nothing here uses the parity word.

## The three facts

*Every divisor of a gap is prime to six.*  `G` is even minus odd, so odd; and
`3 ∣ 3 ^ a` while `3 ∤ 2 ^ L`, so `3 ∤ G`.  Divisibility is transitive, so no
divisor of `G` is divisible by `2` or by `3` — in particular every prime factor
of `G` is at least `5`, and every nontrivial divisor is at least `5`.  This is
`gap_divisor_odd`, `gap_divisor_not_three`, `gap_divisor_ge_five`; no primality
predicate is needed, which is why the statements are about divisors.

*Gaps form a lattice.*  For a fixed modulus `m`, the set of exponent pairs
`(L, a)` with `m ∣ 2 ^ L − 3 ^ a` is closed under addition:

`2 ^ (L+K) − 3 ^ (a+b) = 2 ^ L · (2 ^ K − 3 ^ b) + 3 ^ b · (2 ^ L − 3 ^ a)`.

That is `gap_add_dvd`, and iterating it gives `gap_dvd_scale`: the gap of
`(L, a)` divides the gap of `(kL, ka)`.  So a cycle word repeated `k` times has
a gap that is a multiple of the original gap — the arithmetic reason
non-primitive cycles carry no new information.  (The subtractive direction needs
to cancel a power of three, i.e. Euclid's lemma, which is not available here.)

*Which small primes divide a gap is decided by `(L, a)` modulo a fixed number.*
Because `F_p^*` is cyclic, `2 ^ L ≡ 3 ^ a (mod p)` cuts out a sublattice of
index `lcm(ord_p 2, ord_p 3)`.  Three instances are proved here, each by the
`GapOne` method — carry the residue and the exponent's residue together through
one induction:

* `5 ∣ 2 ^ L − 3 ^ a ↔ (L + a) % 4 = 0`     (`ord 2 = ord 3 = 4`)
* `7 ∣ 2 ^ L − 3 ^ a ↔ (a + 4 * L) % 6 = 0`  (`ord 2 = 3`, `ord 3 = 6`)
* `13 ∣ 2 ^ L − 3 ^ a ↔ (L + 8 * a) % 12 = 0` (`ord 2 = 12`, `ord 3 = 3`)

Composed with `cycle_gap_dvd` each becomes a divisibility statement about the
*accumulator* of a hypothetical cycle: e.g. a cycle whose length and odd-step
count sum to a multiple of four has `5 ∣ C_L(n)`.

## What this does not buy

The conditions `p ∣ C` for the `ω(G)` primes of `G` are, by the Chinese
remainder theorem, *the single condition* `G ∣ C` — splitting `G` into primes
adds no constraint.  Measured: `ω(2 ^ L − 3 ^ a)` for `a/L` near `log 3 / log 2`
grows only like `log L` (mean `1.85` for `L < 40`, `5.00` for `160 ≤ L < 200`),
and `2 ^ L − 3 ^ a` is *prime* at `(L, a) = (89, 56), (97, 61), (110, 69),
(116, 73), (121, 76)`.  So a gap need not have many prime factors at all.
-/

namespace Collatz
namespace GapPrimes

open Congruence AffineExact AccCycle CycleAccumulator

/-! ## Every divisor of a gap is prime to six -/

/-- A gap is odd: even minus odd. -/
theorem gap_odd {L a : Nat} (hL : 1 ≤ L) (ha : 1 ≤ a) (hlt : 3 ^ a < 2 ^ L) :
    (2 ^ L - 3 ^ a) % 2 = 1 := by
  have h2 : 2 ^ L = 2 * 2 ^ (L - 1) := by
    rw [← Arith.two_pow_succ]
    congr 1
    omega
  have h3 : 3 ^ a = 3 * 3 ^ (a - 1) := by
    rw [← Arith.three_pow_succ]
    congr 1
    omega
  have h3' : 3 ^ (a - 1) % 2 = 1 := by
    have : ∀ k, 3 ^ k % 2 = 1 := by
      intro k
      induction k with
      | zero => decide
      | succ k ih =>
        have hs : 3 ^ (k + 1) = 3 * 3 ^ k := Arith.three_pow_succ k
        omega
    exact this _
  omega

/-- A gap is not divisible by three: `3 ∣ 3 ^ a` for `a ≥ 1`, and `2 ^ L` is
`1` or `2` mod three. -/
theorem gap_not_three {L a : Nat} (ha : 1 ≤ a) (hlt : 3 ^ a < 2 ^ L) :
    (2 ^ L - 3 ^ a) % 3 ≠ 0 := by
  have h3 := GapOne.three_pow_mod_three ha
  have h2 := GapOne.two_pow_mod_three L
  omega

/-- **Every divisor of a gap is odd.** -/
theorem gap_divisor_odd {L a d : Nat} (hL : 1 ≤ L) (ha : 1 ≤ a) (hlt : 3 ^ a < 2 ^ L)
    (hd : d ∣ 2 ^ L - 3 ^ a) : d % 2 = 1 := by
  have hg := gap_odd hL ha hlt
  obtain ⟨k, hk⟩ := hd
  have hcase : d % 2 = 0 ∨ d % 2 = 1 := by omega
  rcases hcase with h0 | h1
  · exfalso
    obtain ⟨t, ht⟩ : ∃ t, d = 2 * t := ⟨d / 2, by omega⟩
    have : 2 ^ L - 3 ^ a = 2 * (t * k) := by rw [hk, ht, Nat.mul_assoc]
    omega
  · exact h1

/-- **No divisor of a gap is a multiple of three.** -/
theorem gap_divisor_not_three {L a d : Nat} (ha : 1 ≤ a) (hlt : 3 ^ a < 2 ^ L)
    (hd : d ∣ 2 ^ L - 3 ^ a) : d % 3 ≠ 0 := by
  intro h3
  have hg := gap_not_three ha hlt
  obtain ⟨k, hk⟩ := hd
  obtain ⟨t, ht⟩ : ∃ t, d = 3 * t := ⟨d / 3, by omega⟩
  apply hg
  rw [hk, ht, Nat.mul_assoc]
  omega

/-- **Every divisor of a gap other than one is at least five.**  It is odd and
not a multiple of three, so it avoids `2`, `3` and `4`. -/
theorem gap_divisor_ge_five {L a d : Nat} (hL : 1 ≤ L) (ha : 1 ≤ a) (hlt : 3 ^ a < 2 ^ L)
    (hd : d ∣ 2 ^ L - 3 ^ a) (hd1 : d ≠ 1) (hd0 : d ≠ 0) : 5 ≤ d := by
  have h2 := gap_divisor_odd hL ha hlt hd
  have h3 := gap_divisor_not_three ha hlt hd
  omega

/-! ## Gaps form a lattice -/

/-- The one piece of ring normalisation the lattice law needs. -/
theorem mul_expand (X P Y Q : Nat) :
    (X + P) * (Y + Q) = X * Y + (X * Q + (P * Y + P * Q)) := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  omega

/-- **The gap lattice, additive law.**  If a modulus divides the gap at `(L, a)`
and at `(K, b)` then it divides the gap at `(L + K, a + b)`.  The identity is

`2 ^ (L+K) − 3 ^ (a+b) = 3 ^ a · (2 ^ K − 3 ^ b) + (2 ^ L − 3 ^ a) · 3 ^ b
                        + (2 ^ L − 3 ^ a) · (2 ^ K − 3 ^ b)`. -/
theorem gap_add_dvd {m L a K b : Nat} (h1le : 3 ^ a ≤ 2 ^ L) (h2le : 3 ^ b ≤ 2 ^ K)
    (h1 : m ∣ 2 ^ L - 3 ^ a) (h2 : m ∣ 2 ^ K - 3 ^ b) :
    m ∣ 2 ^ (L + K) - 3 ^ (a + b) := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  have hp : 2 ^ L = 3 ^ a + m * s := by omega
  have hq : 2 ^ K = 3 ^ b + m * t := by omega
  have hexp : 2 ^ (L + K)
      = 3 ^ (a + b) + (3 ^ a * (m * t) + ((m * s) * 3 ^ b + (m * s) * (m * t))) := by
    rw [Arith.two_pow_add, Arith.three_pow_add, hp, hq, mul_expand]
  have hdvd : m ∣ 3 ^ a * (m * t) + ((m * s) * 3 ^ b + (m * s) * (m * t)) := by
    refine ⟨3 ^ a * t + (s * 3 ^ b + s * (m * t)), ?_⟩
    simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hrw : 2 ^ (L + K) - 3 ^ (a + b)
      = 3 ^ a * (m * t) + ((m * s) * 3 ^ b + (m * s) * (m * t)) := by omega
  rw [hrw]
  exact hdvd

/-- Ordering is preserved by the lattice law, so it can be iterated. -/
theorem three_pow_le_two_pow_add {L a K b : Nat} (h1le : 3 ^ a ≤ 2 ^ L)
    (h2le : 3 ^ b ≤ 2 ^ K) : 3 ^ (a + b) ≤ 2 ^ (L + K) := by
  rw [Arith.two_pow_add, Arith.three_pow_add]
  exact Nat.mul_le_mul h1le h2le

/-- **A gap divides every scaled gap.**  `2 ^ L − 3 ^ a ∣ 2 ^ (kL) − 3 ^ (ka)`:
repeating a word `k` times multiplies its gap.  This is why non-primitive cycles
supply no new divisibility. -/
theorem gap_dvd_scale {L a : Nat} (hle : 3 ^ a ≤ 2 ^ L) :
    ∀ k, 3 ^ (k * a) ≤ 2 ^ (k * L) ∧ (2 ^ L - 3 ^ a) ∣ 2 ^ (k * L) - 3 ^ (k * a) := by
  intro k
  induction k with
  | zero => exact ⟨by simp, by simp⟩
  | succ k ih =>
    rw [Nat.succ_mul, Nat.succ_mul]
    exact ⟨three_pow_le_two_pow_add ih.1 hle,
      gap_add_dvd ih.1 hle ih.2 (Nat.dvd_refl _)⟩

/-! ## Which small primes divide a gap -/

/-- The residue of `2 ^ L` mod five, coupled to `L` mod four. -/
theorem two_pow_res_five (L : Nat) :
    (L % 4 = 0 ∧ 2 ^ L % 5 = 1) ∨ (L % 4 = 1 ∧ 2 ^ L % 5 = 2) ∨
      (L % 4 = 2 ∧ 2 ^ L % 5 = 4) ∨ (L % 4 = 3 ∧ 2 ^ L % 5 = 3) := by
  induction L with
  | zero => left; exact ⟨by decide, by decide⟩
  | succ L ih =>
    have hs : 2 ^ (L + 1) = 2 * 2 ^ L := Arith.two_pow_succ L
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- The residue of `3 ^ a` mod five, coupled to `a` mod four. -/
theorem three_pow_res_five (a : Nat) :
    (a % 4 = 0 ∧ 3 ^ a % 5 = 1) ∨ (a % 4 = 1 ∧ 3 ^ a % 5 = 3) ∨
      (a % 4 = 2 ∧ 3 ^ a % 5 = 4) ∨ (a % 4 = 3 ∧ 3 ^ a % 5 = 2) := by
  induction a with
  | zero => left; exact ⟨by decide, by decide⟩
  | succ a ih =>
    have hs : 3 ^ (a + 1) = 3 * 3 ^ a := Arith.three_pow_succ a
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- **Five divides the gap exactly when `L + a` is a multiple of four.**  Both
`2` and `3` have order four mod five, and `3 = 2 ^ 3`, so `2 ^ L ≡ 3 ^ a` reads
`L ≡ 3a`, i.e. `L + a ≡ 0 (mod 4)`. -/
theorem five_dvd_gap_iff {L a : Nat} (hle : 3 ^ a ≤ 2 ^ L) :
    5 ∣ 2 ^ L - 3 ^ a ↔ (L + a) % 4 = 0 := by
  have h2 := two_pow_res_five L
  have h3 := three_pow_res_five a
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    rcases h2 with ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ <;>
      rcases h3 with ⟨q1, q2⟩ | ⟨q1, q2⟩ | ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> omega
  · intro h
    refine ⟨(2 ^ L - 3 ^ a) / 5, ?_⟩
    rcases h2 with ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ <;>
      rcases h3 with ⟨q1, q2⟩ | ⟨q1, q2⟩ | ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> omega

/-- The residue of `2 ^ L` mod seven, coupled to `L` mod three. -/
theorem two_pow_res_seven (L : Nat) :
    (L % 3 = 0 ∧ 2 ^ L % 7 = 1) ∨ (L % 3 = 1 ∧ 2 ^ L % 7 = 2) ∨
      (L % 3 = 2 ∧ 2 ^ L % 7 = 4) := by
  induction L with
  | zero => left; exact ⟨by decide, by decide⟩
  | succ L ih =>
    have hs : 2 ^ (L + 1) = 2 * 2 ^ L := Arith.two_pow_succ L
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- The residue of `3 ^ a` mod seven, coupled to `a` mod six. -/
theorem three_pow_res_seven (a : Nat) :
    (a % 6 = 0 ∧ 3 ^ a % 7 = 1) ∨ (a % 6 = 1 ∧ 3 ^ a % 7 = 3) ∨
      (a % 6 = 2 ∧ 3 ^ a % 7 = 2) ∨ (a % 6 = 3 ∧ 3 ^ a % 7 = 6) ∨
      (a % 6 = 4 ∧ 3 ^ a % 7 = 4) ∨ (a % 6 = 5 ∧ 3 ^ a % 7 = 5) := by
  induction a with
  | zero => left; exact ⟨by decide, by decide⟩
  | succ a ih =>
    have hs : 3 ^ (a + 1) = 3 * 3 ^ a := Arith.three_pow_succ a
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

set_option maxHeartbeats 1000000 in
/-- **Seven divides the gap exactly when `a ≡ 2L (mod 6)`.** -/
theorem seven_dvd_gap_iff {L a : Nat} (hle : 3 ^ a ≤ 2 ^ L) :
    7 ∣ 2 ^ L - 3 ^ a ↔ (a + 4 * L) % 6 = 0 := by
  have h2 := two_pow_res_seven L
  have h3 := three_pow_res_seven a
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    rcases h2 with ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ <;>
      rcases h3 with ⟨q1, q2⟩ | ⟨q1, q2⟩ | ⟨q1, q2⟩ | ⟨q1, q2⟩ | ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> omega
  · intro h
    refine ⟨(2 ^ L - 3 ^ a) / 7, ?_⟩
    rcases h2 with ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ <;>
      rcases h3 with ⟨q1, q2⟩ | ⟨q1, q2⟩ | ⟨q1, q2⟩ | ⟨q1, q2⟩ | ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> omega

/-- The residue of `3 ^ a` mod thirteen, coupled to `a` mod three. -/
theorem three_pow_res_thirteen (a : Nat) :
    (a % 3 = 0 ∧ 3 ^ a % 13 = 1) ∨ (a % 3 = 1 ∧ 3 ^ a % 13 = 3) ∨
      (a % 3 = 2 ∧ 3 ^ a % 13 = 9) := by
  induction a with
  | zero => left; exact ⟨by decide, by decide⟩
  | succ a ih =>
    have hs : 3 ^ (a + 1) = 3 * 3 ^ a := Arith.three_pow_succ a
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

set_option maxHeartbeats 2000000 in
/-- The residue of `2 ^ L` mod thirteen, coupled to `L` mod twelve. -/
theorem two_pow_res_thirteen (L : Nat) :
    (L % 12 = 0 ∧ 2 ^ L % 13 = 1) ∨ (L % 12 = 1 ∧ 2 ^ L % 13 = 2) ∨
      (L % 12 = 2 ∧ 2 ^ L % 13 = 4) ∨ (L % 12 = 3 ∧ 2 ^ L % 13 = 8) ∨
      (L % 12 = 4 ∧ 2 ^ L % 13 = 3) ∨ (L % 12 = 5 ∧ 2 ^ L % 13 = 6) ∨
      (L % 12 = 6 ∧ 2 ^ L % 13 = 12) ∨ (L % 12 = 7 ∧ 2 ^ L % 13 = 11) ∨
      (L % 12 = 8 ∧ 2 ^ L % 13 = 9) ∨ (L % 12 = 9 ∧ 2 ^ L % 13 = 5) ∨
      (L % 12 = 10 ∧ 2 ^ L % 13 = 10) ∨ (L % 12 = 11 ∧ 2 ^ L % 13 = 7) := by
  induction L with
  | zero => left; exact ⟨by decide, by decide⟩
  | succ L ih =>
    have hs : 2 ^ (L + 1) = 2 * 2 ^ L := Arith.two_pow_succ L
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

set_option maxHeartbeats 2000000 in
/-- **Thirteen divides the gap exactly when `L ≡ 4a (mod 12)`.** -/
theorem thirteen_dvd_gap_iff {L a : Nat} (hle : 3 ^ a ≤ 2 ^ L) :
    13 ∣ 2 ^ L - 3 ^ a ↔ (L + 8 * a) % 12 = 0 := by
  have h2 := two_pow_res_thirteen L
  have h3 := three_pow_res_thirteen a
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    rcases h3 with ⟨q1, q2⟩ | ⟨q1, q2⟩ | ⟨q1, q2⟩ <;>
      rcases h2 with ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ |
        ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ <;> omega
  · intro h
    refine ⟨(2 ^ L - 3 ^ a) / 13, ?_⟩
    rcases h3 with ⟨q1, q2⟩ | ⟨q1, q2⟩ | ⟨q1, q2⟩ <;>
      rcases h2 with ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ |
        ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ <;> omega

/-! ## What this says about a hypothetical cycle -/

/-- Every divisor of a cycle's gap, other than one, is at least five — in
particular every prime factor of the gap is at least five. -/
theorem cycle_gap_divisor_ge_five {n L d : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hd : d ∣ 2 ^ L - 3 ^ oddCount n L) (hd1 : d ≠ 1) (hd0 : d ≠ 0) : 5 ≤ d := by
  obtain ⟨ha, _, hlt⟩ := accCycle_bounds hn h
  exact gap_divisor_ge_five h.1 ha hlt hd hd1 hd0

/-- **A cycle whose length and odd-step count sum to a multiple of four has an
accumulator divisible by five.**  Composition of `five_dvd_gap_iff` with
`cycle_gap_dvd`. -/
theorem cycle_five_dvd_affineC {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hmod : (L + oddCount n L) % 4 = 0) : 5 ∣ affineC L n := by
  obtain ⟨_, _, hlt⟩ := accCycle_bounds hn h
  have h5 : (5 : Nat) ∣ 2 ^ L - 3 ^ oddCount n L :=
    (five_dvd_gap_iff (by omega)).mpr hmod
  exact Nat.dvd_trans h5 (cycle_gap_dvd hn h)

/-- The mod-seven companion. -/
theorem cycle_seven_dvd_affineC {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hmod : (oddCount n L + 4 * L) % 6 = 0) : 7 ∣ affineC L n := by
  obtain ⟨_, _, hlt⟩ := accCycle_bounds hn h
  have h7 : (7 : Nat) ∣ 2 ^ L - 3 ^ oddCount n L :=
    (seven_dvd_gap_iff (by omega)).mpr hmod
  exact Nat.dvd_trans h7 (cycle_gap_dvd hn h)

/-- The mod-thirteen companion. -/
theorem cycle_thirteen_dvd_affineC {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hmod : (L + 8 * oddCount n L) % 12 = 0) : 13 ∣ affineC L n := by
  obtain ⟨_, _, hlt⟩ := accCycle_bounds hn h
  have h13 : (13 : Nat) ∣ 2 ^ L - 3 ^ oddCount n L :=
    (thirteen_dvd_gap_iff (by omega)).mpr hmod
  exact Nat.dvd_trans h13 (cycle_gap_dvd hn h)

/-- **The gap of a cycle divides every scaled gap.**  Concretely: the gap of a
cycle of length `L` with `a` odd steps divides `2 ^ (kL) − 3 ^ (ka)` for every
`k`, so a cycle constrains the whole arithmetic progression of exponent pairs it
generates, not just its own. -/
theorem cycle_gap_dvd_scale {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) (k : Nat) :
    (2 ^ L - 3 ^ oddCount n L) ∣ 2 ^ (k * L) - 3 ^ (k * oddCount n L) := by
  obtain ⟨_, _, hlt⟩ := accCycle_bounds hn h
  exact (gap_dvd_scale (by omega) k).2

end GapPrimes
end Collatz
