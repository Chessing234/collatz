import Collatz.Strategy.OrbitWindows

/-!
# The master bound is invariant under forward odd runs

`BackwardRun.orbit_backward_bound` constrains an orbit point `v` through the
3-adic valuation of `v + 1`.  A natural hope is to *push it forward*: apply it at
`T(v)`, at `T²(v)`, and so on, accumulating constraints.

That hope is empty, and this file proves it.

## The peak lemma

For odd `x` write `A` for the length of its odd run (so `2 ^ A ∣ x + 1`) and let
`3 ^ B ∣ x + 1`.  Then

`3 ^ (A + B) ∣ (T^A(x) + 1)`   (`three_pow_dvd_run_end`)

— the 3-adic valuation at the top of the run is the sum of the two valuations at
the bottom, because each odd step adds one (`ThreeAdic.three_pow_odd_step_iff`)
and the run identity `2 ^ A (T^A(x)+1) = 3 ^ A (x+1)` carries the rest.

## The invariance

Applying the master bound at the peak with `j = A + B` is then **exactly
equivalent** to applying it at `x` with `j = B`:

`3 ^ (A+B) · M ≤ 2 ^ (A+B) · (T^A(x) + 1)  ↔  3 ^ B · M ≤ 2 ^ B · (x + 1)`

(`bound_invariant_under_run`).  The factor `3 ^ A` cancels off both sides.

So the master bound gains **nothing** from forward odd steps: every odd run
carries it forward with slack exactly zero.  This explains the observed sharpness
at `T(m)` and `T²(m)` — those are not lucky coincidences but instances of an
identity, and it means the whole ladder of "apply the bound one step later" is
a single statement repeated.

**All new information must therefore come from even steps.**  That is where the
3-adic valuation is not merely transported but *recreated*
(`ThreeAdic.three_dvd_even_step_iff`), and it is the only place left in an
excursion where the bound can bite.

A small companion fact: `x + 1` and `x + 2` are never both divisible by three
(they differ by one), so the first even step after a peak always starts from
valuation zero and is automatically safe.
-/

namespace Collatz
namespace RunInvariance

open Reach Congruence NeverDrops

/-! ## Coprimality, iterated -/

/-- A power of three dividing `2 ^ A · y` divides `y`. -/
theorem dvd_of_two_pow_mul : ∀ (A k y : Nat), 3 ^ k ∣ 2 ^ A * y → 3 ^ k ∣ y := by
  intro A
  induction A with
  | zero => intro k y h; simpa using h
  | succ A ih =>
    intro k y h
    refine ih k y ?_
    refine ThreeAdic.dvd_of_two_mul k (2 ^ A * y) ?_
    have hsplit : (2:Nat) ^ (A + 1) * y = 2 * (2 ^ A * y) := by
      rw [Arith.two_pow_succ, Nat.mul_assoc]
    rw [← hsplit]
    exact h

/-! ## The peak lemma -/

/-- **The valuation at the top of a run is the sum of the valuations at the
bottom.**  If `x` takes `A` odd steps and `3 ^ B ∣ (x + 1)`, then
`3 ^ (A + B) ∣ (T^A(x) + 1)`. -/
theorem three_pow_dvd_run_end {x A B : Nat} (hrun : OddRuns.OddRun x A)
    (hB : 3 ^ B ∣ (x + 1)) : 3 ^ (A + B) ∣ (acceleratedOrbit A x + 1) := by
  have hval : 2 ^ A * (acceleratedOrbit A x + 1) = 3 ^ A * (x + 1) :=
    RunValue.oddRun_value A x hrun
  obtain ⟨c, hc⟩ := hB
  refine dvd_of_two_pow_mul A (A + B) _ ⟨c, ?_⟩
  rw [hval, hc, Nat.pow_add, Nat.mul_assoc]

/-! ## The invariance -/

/-- **The master bound is invariant under forward odd runs.**  Its instance at
the top of a run of length `A`, at level `A + B`, is *equivalent* to its instance
at the bottom at level `B`.  The factor `3 ^ A` cancels. -/
theorem bound_invariant_under_run {x A B M : Nat} (hrun : OddRuns.OddRun x A) :
    (3 ^ (A + B) * M ≤ 2 ^ (A + B) * (acceleratedOrbit A x + 1)) ↔
    (3 ^ B * M ≤ 2 ^ B * (x + 1)) := by
  have hval : 2 ^ A * (acceleratedOrbit A x + 1) = 3 ^ A * (x + 1) :=
    RunValue.oddRun_value A x hrun
  have hL : (3:Nat) ^ (A + B) * M = 3 ^ A * (3 ^ B * M) := by
    rw [Nat.pow_add, Nat.mul_assoc]
  have hR : (2:Nat) ^ (A + B) * (acceleratedOrbit A x + 1)
      = 2 ^ B * (2 ^ A * (acceleratedOrbit A x + 1)) := by
    rw [Nat.pow_add, Nat.mul_comm ((2:Nat) ^ A) ((2:Nat) ^ B), Nat.mul_assoc]
  rw [hL, hR, hval]
  have hcomm : (2:Nat) ^ B * (3 ^ A * (x + 1)) = 3 ^ A * (2 ^ B * (x + 1)) := by
    rw [Nat.mul_left_comm]
  rw [hcomm]
  constructor
  · intro h
    exact Nat.le_of_mul_le_mul_left h (Arith.three_pow_pos A)
  · intro h
    exact Nat.mul_le_mul_left _ h

/-- Restated as the fact it establishes: pushing the bound through an odd run
produces the same constraint, so no ladder of forward applications is stronger
than its first rung. -/
theorem no_gain_from_odd_steps {m x A B : Nat} (hrun : OddRuns.OddRun x A)
    (hbot : ¬ (3 ^ B * (m + 1) ≤ 2 ^ B * (x + 1))) :
    ¬ (3 ^ (A + B) * (m + 1) ≤ 2 ^ (A + B) * (acceleratedOrbit A x + 1)) := by
  intro h
  exact hbot ((bound_invariant_under_run hrun).mp h)

/-! ## The companion disjointness -/

/-- `x + 1` and `x + 2` are never both divisible by three, so the first even step
after a run always starts from 3-adic valuation zero. -/
theorem three_dvd_disjoint (x : Nat) : ¬ (3 ∣ (x + 1) ∧ 3 ∣ (x + 2)) := by
  intro ⟨h1, h2⟩
  omega

/-- **Where the remaining information lives.**  Odd steps transport the bound
with zero slack; even steps are the only place the 3-adic valuation is created,
and there it is created from zero. -/
theorem information_only_at_even_steps {x A B M : Nat} (hrun : OddRuns.OddRun x A) :
    ((3 ^ (A + B) * M ≤ 2 ^ (A + B) * (acceleratedOrbit A x + 1)) ↔
      (3 ^ B * M ≤ 2 ^ B * (x + 1))) ∧
    (∀ y : Nat, ¬ (3 ∣ (y + 1) ∧ 3 ∣ (y + 2))) :=
  ⟨bound_invariant_under_run hrun, three_dvd_disjoint⟩

end RunInvariance
end Collatz
