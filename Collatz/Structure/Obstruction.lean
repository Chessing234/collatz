import Collatz.Structure.Congruence

/-!
# An obstruction: the sieve can never clear

The residue sieve of `Collatz.Structure.Minimal` removes congruence classes at a
good rate, and it is tempting to hope that for some modulus `2 ^ K` *every* class
descends, which would finish the conjecture outright.

This file proves that this hope is false, for every `K`.

The obstruction is the class `-1` modulo `2 ^ K`.  Starting from `2 ^ K - 1`,
the accelerated map takes `K` consecutive **odd** steps:

`3^a · 2^b − 1  ↦  3^{a+1} · 2^{b−1} − 1`

so after `i` steps the state is `3^i · 2^{K−i} − 1`, and the multiplier attached
to the class is `3 ^ K`, which exceeds `2 ^ K`.  The class therefore grows, and
no amount of increasing `K` helps: `2 ^ K − 1` survives at every level.

The consequence, `sieve_never_clears`, is a genuine negative result about the
method: elementary residue descent alone cannot prove Collatz, and any complete
proof must treat the `-1` classes by other means.  Knowing precisely where a
method dies is worth as much as knowing where it works.
-/

namespace Collatz
namespace Obstruction

open Reach Congruence

/-! ## The `-1` classes are closed under the accelerated map -/

/-- Numbers of the form `3 ^ a · 2 ^ b − 1` with `b > 0` are odd. -/
theorem odd_three_pow_mul_two_pow_sub_one {a b : Nat} (hb : 0 < b) :
    (3 ^ a * 2 ^ b - 1) % 2 = 1 := by
  have hR : 3 ^ a * 2 ^ b = 2 * (3 ^ a * 2 ^ (b - 1)) := by
    have h1 : (2:Nat) ^ b = 2 * 2 ^ (b - 1) := by
      have hb' : b - 1 + 1 = b := by omega
      rw [← hb', Arith.two_pow_succ]
      simp
    rw [h1, Nat.mul_left_comm]
  have hpos : 0 < 3 ^ a * 2 ^ (b - 1) :=
    Nat.mul_pos (Arith.three_pow_pos a) (Arith.two_pow_pos (b - 1))
  omega

/-- **One step inside the `-1` classes.**  The accelerated map sends
`3 ^ a · 2 ^ b − 1` to `3 ^ (a+1) · 2 ^ (b−1) − 1`: the power of three grows and
the power of two shrinks. -/
theorem accStep_three_pow_mul_two_pow_sub_one {a b : Nat} (hb : 0 < b) :
    acceleratedStep (3 ^ a * 2 ^ b - 1) = 3 ^ (a + 1) * 2 ^ (b - 1) - 1 := by
  have hR : 3 ^ a * 2 ^ b = 2 * (3 ^ a * 2 ^ (b - 1)) := by
    have h1 : (2:Nat) ^ b = 2 * 2 ^ (b - 1) := by
      have hb' : b - 1 + 1 = b := by omega
      rw [← hb', Arith.two_pow_succ]
      simp
    rw [h1, Nat.mul_left_comm]
  have hT : 3 ^ (a + 1) * 2 ^ (b - 1) = 3 * (3 ^ a * 2 ^ (b - 1)) := by
    rw [Arith.three_pow_succ, Nat.mul_assoc]
  have hpos : 0 < 3 ^ a * 2 ^ (b - 1) :=
    Nat.mul_pos (Arith.three_pow_pos a) (Arith.two_pow_pos (b - 1))
  have hodd := odd_three_pow_mul_two_pow_sub_one (a := a) hb
  rw [acceleratedStep, if_neg (by omega), hT]
  omega

/-- **The orbit of `2 ^ K − 1`.**  After `i ≤ K` accelerated steps the state is
`3 ^ i · 2 ^ (K − i) − 1`; stated additively to avoid truncated subtraction. -/
theorem accOrbit_two_pow_sub_one {K : Nat} : ∀ i : Nat, i ≤ K →
    acceleratedOrbit i (2 ^ K - 1) + 1 = 3 ^ i * 2 ^ (K - i) := by
  intro i
  induction i with
  | zero =>
    intro _
    have := Arith.two_pow_pos K
    simp [acceleratedOrbit]
    omega
  | succ i ih =>
    intro hi
    have hik : i ≤ K := by omega
    have hprev := ih hik
    have hpos : 0 < 3 ^ i * 2 ^ (K - i) :=
      Nat.mul_pos (Arith.three_pow_pos i) (Arith.two_pow_pos (K - i))
    have heq : acceleratedOrbit i (2 ^ K - 1) = 3 ^ i * 2 ^ (K - i) - 1 := by omega
    have hb : 0 < K - i := by omega
    have hstep := accStep_three_pow_mul_two_pow_sub_one (a := i) (b := K - i) hb
    have hidx : K - i - 1 = K - (i + 1) := by omega
    have hpos' : 0 < 3 ^ (i + 1) * 2 ^ (K - (i + 1)) :=
      Nat.mul_pos (Arith.three_pow_pos (i + 1)) (Arith.two_pow_pos (K - (i + 1)))
    rw [acceleratedOrbit_succ_step, heq, hstep, hidx]
    omega

/-- Every one of the first `K` steps out of `2 ^ K − 1` is an odd step, stated
in the general `3 ^ a · 2 ^ b − 1` form. -/
theorem oddCount_three_pow_mul_two_pow_sub_one (b : Nat) : ∀ a : Nat,
    oddCount (3 ^ a * 2 ^ b - 1) b = b := by
  induction b with
  | zero => intro a; simp
  | succ b ih =>
    intro a
    have hodd := odd_three_pow_mul_two_pow_sub_one (a := a) (b := b + 1) (by omega)
    have hstep := accStep_three_pow_mul_two_pow_sub_one (a := a) (b := b + 1) (by omega)
    have hidx : b + 1 - 1 = b := by omega
    rw [oddCount_succ_of_odd hodd, hstep, hidx, ih (a + 1)]

/-- The odd-step count of `2 ^ K − 1` over `K` steps is `K`: the class is
*maximally* expanding. -/
theorem oddCount_two_pow_sub_one (K : Nat) : oddCount (2 ^ K - 1) K = K := by
  have h := oddCount_three_pow_mul_two_pow_sub_one K 0
  simpa using h

/-! ## The obstruction -/

/-- Powers of three strictly dominate powers of two above exponent zero. -/
theorem two_pow_lt_three_pow {K : Nat} (hK : 0 < K) : 2 ^ K < 3 ^ K :=
  Nat.pow_lt_pow_left (by omega) (by omega)

/-- **The `-1` class never descends.**  For every positive `K` the residue
`2 ^ K − 1` fails the descent criterion at level `K`. -/
theorem not_descends_two_pow_sub_one {K : Nat} (hK : 0 < K) :
    ¬ Descends K (2 ^ K - 1) := by
  intro h
  have hmul := h.1
  rw [oddCount_two_pow_sub_one] at hmul
  have := two_pow_lt_three_pow hK
  omega

/-- The residue `2 ^ K − 1` reduces to `2 ^ j − 1` at every smaller modulus:
the obstruction is consistent all the way down. -/
theorem two_pow_sub_one_mod {K j : Nat} (hj : j ≤ K) :
    (2 ^ K - 1) % 2 ^ j = 2 ^ j - 1 := by
  have hjpos : 0 < 2 ^ j := Arith.two_pow_pos j
  have hle : 2 ^ j ≤ 2 ^ K := Arith.two_pow_le_two_pow hj
  have h1 : 2 ^ j * 2 ^ (K - j) = 2 ^ K := by
    rw [← Arith.two_pow_add]
    congr 1
    omega
  have h2 : 2 ^ j * (2 ^ (K - j) - 1) = 2 ^ K - 2 ^ j := by
    rw [Nat.mul_sub, Nat.mul_one, h1]
  have hsplit : 2 ^ K - 1 = 2 ^ j * (2 ^ (K - j) - 1) + (2 ^ j - 1) := by
    rw [h2]; omega
  rw [hsplit, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

/-- The obstruction fails the criterion at **every** level, not just the top
one. -/
theorem not_descends_two_pow_sub_one_at {K j : Nat} (hj : j ≤ K) (hjpos : 0 < j) :
    ¬ Descends j ((2 ^ K - 1) % 2 ^ j) := by
  rw [two_pow_sub_one_mod hj]
  exact not_descends_two_pow_sub_one hjpos

/-- The descent criterion is vacuously false at level zero. -/
theorem not_descends_zero (r : Nat) : ¬ Descends 0 r := by
  intro h
  have := h.1
  simp at this

/-- **The sieve never clears.**  For every modulus `2 ^ K` there is a residue —
namely `2 ^ K − 1` — that escapes the descent criterion at every level.  No
choice of `K` makes elementary residue descent settle the conjecture. -/
theorem sieve_never_clears (K : Nat) :
    ∃ r : Nat, r < 2 ^ K ∧ survives K r = true := by
  refine ⟨2 ^ K - 1, by have := Arith.two_pow_pos K; omega, ?_⟩
  refine survives_of_not_descends (fun i hi => ?_)
  cases i with
  | zero => exact not_descends_zero _
  | succ i => exact not_descends_two_pow_sub_one_at (by omega) (by omega)

/-- Equivalently: no `sieveCheck` with an empty allowed list can succeed. -/
theorem sieveCheck_nil_false (K : Nat) : sieveCheck K [] = false := by
  obtain ⟨r, hr, hs⟩ := sieve_never_clears K
  by_cases h : sieveCheck K [] = true
  · have := mem_allowed_of_sieveCheck h hr hs
    simp at this
  · simpa using h

end Obstruction
end Collatz
