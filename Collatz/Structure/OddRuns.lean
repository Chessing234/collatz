import Collatz.Structure.Records

/-!
# Runs of odd steps

Every obstruction in this project has been the same object: the class
`−1 mod 2^k`.  It defeats the residue sieve, it is the heavy residue that
survives the density bound, and it is the one class the cycle-length test never
reaches.  This file explains *why* by characterising it exactly.

**A number takes `j` consecutive odd steps if and only if it is `−1` modulo
`2^j`.**

The forward direction is the useful one: consecutive odd steps are not merely
*possible* for that class, they are *exclusive* to it.  Any number whose first
`j` accelerated steps are all odd is congruent to `2^j − 1` modulo `2^j`, and
conversely.

That pins the obstruction down completely.  Long runs of odd steps — the only
way an orbit can climb persistently — are available to exactly one residue class
per length, and that class is the one every method here fails on.

The proof is the divisibility identity `2(T(x) + 1) = 3(x + 1)` for odd `x`,
which converts a factor of two on one side into a factor of two on the other,
since `3` is invertible modulo every power of two.
-/

namespace Collatz
namespace OddRuns

open Reach Congruence

/-! ## Powers of two are coprime to three -/

/-- A power of two dividing `3 y` divides `y`. -/
theorem dvd_of_three_mul : ∀ (k y : Nat), 2 ^ k ∣ 3 * y → 2 ^ k ∣ y := by
  intro k
  induction k with
  | zero => intro y _; simp
  | succ k ih =>
    intro y hdvd
    -- `3 y` is even, so `y` is even
    have heven : y % 2 = 0 := by
      obtain ⟨c, hc⟩ := hdvd
      have h2 : (2:Nat) ^ (k + 1) = 2 * 2 ^ k := Arith.two_pow_succ k
      rw [h2, Nat.mul_assoc] at hc
      omega
    obtain ⟨y', hy'⟩ : ∃ y', y = 2 * y' := ⟨y / 2, by omega⟩
    subst hy'
    -- strip one factor of two from both sides
    have hstrip : 2 ^ k ∣ 3 * y' := by
      obtain ⟨c, hc⟩ := hdvd
      refine ⟨c, ?_⟩
      have h2 : (2:Nat) ^ (k + 1) = 2 * 2 ^ k := Arith.two_pow_succ k
      rw [h2, Nat.mul_assoc] at hc
      omega
    obtain ⟨d, hd⟩ := ih y' hstrip
    refine ⟨d, ?_⟩
    have hA : (2:Nat) ^ (k + 1) * d = 2 * (2 ^ k * d) := by
      rw [Arith.two_pow_succ, Nat.mul_assoc]
    rw [hA, ← hd]

/-! ## The characterisation -/

/-- `OddRun x j` says the first `j` accelerated steps from `x` are all odd. -/
def OddRun (x j : Nat) : Prop := ∀ i : Nat, i < j → acceleratedOrbit i x % 2 = 1

/-- The step identity behind everything: for odd `x`, `2(T(x) + 1) = 3(x + 1)`. -/
theorem two_mul_succ_step {x : Nat} (hx : x % 2 = 1) :
    2 * (acceleratedStep x + 1) = 3 * (x + 1) := by
  rw [acceleratedStep, if_neg (by omega)]
  omega

/-- **The characterisation of odd runs.**  A number takes `j` consecutive odd
steps exactly when it is `−1` modulo `2 ^ j`. -/
theorem oddRun_iff : ∀ (j x : Nat), OddRun x j ↔ 2 ^ j ∣ (x + 1) := by
  intro j
  induction j with
  | zero =>
    intro x
    constructor
    · intro _; simp
    · intro _ i hi; omega
  | succ j ih =>
    intro x
    constructor
    · intro hrun
      -- `x` is odd, and the next value starts a run of length `j`
      have hx : x % 2 = 1 := by
        have := hrun 0 (by omega)
        rw [acceleratedOrbit] at this
        exact this
      have hnext : OddRun (acceleratedStep x) j := by
        intro i hi
        have := hrun (i + 1) (by omega)
        rw [acceleratedOrbit_succ_step] at this
        -- `T^(i+1)(x) = T^i(T x)` after commuting the step to the front
        have hcomm : acceleratedOrbit i (acceleratedStep x) = acceleratedOrbit (i + 1) x := by
          rw [show i + 1 = i + 1 from rfl, acceleratedOrbit]
        rw [hcomm, acceleratedOrbit_succ_step]
        exact this
      obtain ⟨c, hc⟩ := (ih (acceleratedStep x)).mp hnext
      -- convert through `2(Tx + 1) = 3(x+1)`
      have hid := two_mul_succ_step hx
      rw [hc] at hid
      have hdvd3 : 2 ^ (j + 1) ∣ 3 * (x + 1) := by
        refine ⟨c, ?_⟩
        have hA : (2:Nat) ^ (j + 1) * c = 2 * (2 ^ j * c) := by
          rw [Arith.two_pow_succ, Nat.mul_assoc]
        rw [hA]
        omega
      exact dvd_of_three_mul (j + 1) (x + 1) hdvd3
    · intro hdvd
      -- `x` is odd because `2 ∣ x + 1` with `j + 1 ≥ 1`
      have hx : x % 2 = 1 := by
        obtain ⟨c, hc⟩ := hdvd
        have h2 : (2:Nat) ^ (j + 1) = 2 * 2 ^ j := Arith.two_pow_succ j
        rw [h2, Nat.mul_assoc] at hc
        omega
      -- and the next value is `−1` modulo `2 ^ j`
      have hnext : 2 ^ j ∣ (acceleratedStep x + 1) := by
        obtain ⟨c, hc⟩ := hdvd
        have hA : (2:Nat) ^ (j + 1) * c = 2 * (2 ^ j * c) := by
          rw [Arith.two_pow_succ, Nat.mul_assoc]
        rw [hA] at hc
        have hid := two_mul_succ_step hx
        rw [hc] at hid
        have hexp : 3 * (2 * (2 ^ j * c)) = 2 * (3 * (2 ^ j * c)) := by
          rw [Nat.mul_left_comm]
        rw [hexp] at hid
        refine ⟨3 * c, ?_⟩
        have hcomm : (2:Nat) ^ j * (3 * c) = 3 * (2 ^ j * c) := by
          rw [Nat.mul_left_comm]
        rw [hcomm]
        omega
      have hrun := (ih (acceleratedStep x)).mpr hnext
      intro i hi
      cases i with
      | zero => rw [acceleratedOrbit]; exact hx
      | succ i =>
        have := hrun i (by omega)
        rw [acceleratedOrbit_succ_step, ← acceleratedOrbit_succ_step]
        rw [show acceleratedOrbit (i + 1) x = acceleratedOrbit i (acceleratedStep x) from rfl]
        exact this

/-! ## Consequences -/

/-- The obstruction class realises the longest possible runs: `2 ^ j − 1` takes
`j` consecutive odd steps. -/
theorem oddRun_two_pow_sub_one (j : Nat) : OddRun (2 ^ j - 1) j := by
  refine (oddRun_iff j (2 ^ j - 1)).mpr ?_
  have hpos : 0 < 2 ^ j := Arith.two_pow_pos j
  refine ⟨1, ?_⟩
  omega

/-- **Long runs are exclusive to the obstruction class.**  Anything taking `j`
consecutive odd steps agrees with `2 ^ j − 1` modulo `2 ^ j`. -/
theorem mod_of_oddRun {x j : Nat} (h : OddRun x j) : x % 2 ^ j = 2 ^ j - 1 := by
  obtain ⟨c, hc⟩ := (oddRun_iff j x).mp h
  have hpos : 0 < 2 ^ j := Arith.two_pow_pos j
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · exfalso
      subst h0
      simp at hc
    · exact h0
  have hx : x = 2 ^ j * c - 1 := by omega
  have hsplit : x = 2 ^ j * (c - 1) + (2 ^ j - 1) := by
    have : 2 ^ j * c = 2 ^ j * (c - 1) + 2 ^ j := by
      have hcc : c = (c - 1) + 1 := by omega
      rw [show 2 ^ j * c = 2 ^ j * ((c - 1) + 1) by rw [← hcc], Nat.mul_add, Nat.mul_one]
    omega
  rw [hsplit, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

/-- A run of `j` odd steps forces the number to be at least `2 ^ j − 1`. -/
theorem le_of_oddRun {x j : Nat} (_hx : 0 < x) (h : OddRun x j) : 2 ^ j - 1 ≤ x := by
  have hmod := mod_of_oddRun h
  have hle : x % 2 ^ j ≤ x := Nat.mod_le x (2 ^ j)
  omega

/-- **Climbing is rationed.**  An orbit can only rise `j` steps in a row from `x`
if `x` is at least `2 ^ j − 1`, so persistent climbing requires exponentially
large starting values.  This is the precise sense in which the obstruction class
is the only route upward. -/
theorem climb_bounded {x j : Nat} (hx : 0 < x) (h : OddRun x j) : 2 ^ j ≤ x + 1 := by
  have := le_of_oddRun hx h
  have hpos : 0 < 2 ^ j := Arith.two_pow_pos j
  omega

end OddRuns
end Collatz
