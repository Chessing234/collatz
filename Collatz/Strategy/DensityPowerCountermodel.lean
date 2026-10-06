import Collatz.Strategy.DensityCompatibilityModel
import Collatz.Structure.DensitySeparation

/-!
# Power-threshold density and the order of quantifiers

This is the halving comparison map fixing 1 and 3, not Collatz. Every fixed
positive rational-power target is reached for a cofinite set of inputs, yet
a positive proportion of inputs never reach 1. At a fixed input above one,
reaching every reciprocal-power target is equivalent to reaching 1.
-/
namespace Collatz.DensityCountermodel.PowerComparison
open NaturalDensity Compatibility

/-- The power-threshold predicate for the comparison map only. -/
def BelowPower (p q n : Nat) : Prop := ∃ k, (orbit k n)^q<n^p

/-- Every fixed threshold holds beyond an explicit finite cutoff. -/
theorem below_power_eventually {p q n : Nat} (hp : 0<p) (hn : 3^q+1≤n) :
    BelowPower p q n := by
  have hpowpos : 0<(3:Nat)^q := Nat.pow_pos (by decide)
  obtain ⟨k, hk⟩ := orbit_below_three (by omega : 0<n)
  have hl := Nat.pow_le_pow_left hk q
  have hr : n≤n^p := by
    simpa using Nat.pow_le_pow_right (by omega : 1≤n) hp
  exact ⟨k, by omega⟩

/-- In this model, every fixed positive rational-power target holds with
natural density one, including exponents arbitrarily close to zero. -/
theorem below_power_density_one (p q : Nat) (hp : 0<p) : DensityOne (BelowPower p q) :=
  densityOne_of_eventually (B := 3^q+1) (fun _ hn => below_power_eventually hp hn)

/-- Positivity is preserved along comparison orbits. -/
theorem orbit_positive {n : Nat} (hn : 0<n) (k : Nat) : 0<orbit k n := by
  induction k generalizing n with
  | zero => exact hn
  | succ k ih => exact ih (step_positive hn)

/-- At a fixed start, all reciprocal-power bounds are equivalent to reaching
1. Moving the quantifier over exponents inside density one changes the claim. -/
theorem reaches_one_iff_all_powers {n : Nat} (hn : 1<n) :
    (∃ k, orbit k n=1) ↔ ∀ q, 0<q → BelowPower 1 q n := by
  constructor
  · rintro ⟨k, hk⟩ q _
    exact ⟨k, by simp only [hk, Nat.one_pow, Nat.pow_one]; exact hn⟩
  · intro h
    obtain ⟨k, hk⟩ := h n (by omega)
    have hpos := orbit_positive (by omega : 0<n) k
    by_cases he : orbit k n=1
    · exact ⟨k, he⟩
    · have htwo : 2≤orbit k n := by omega
      have hpow := Nat.pow_le_pow_left htwo n
      have hlarge : n<2^n := Nat.lt_two_pow_self
      simp only [Nat.pow_one] at hk
      omega

/-- Convergence to 1 fails to have natural density one in this model. -/
theorem not_density_one_reaches_one : ¬DensityOne (fun n => ∃ k, orbit k n=1) := by
  apply not_densityOne_of_complement_lower 8 4
  intro N hn
  have hsub := predicateCount_mono
    (P := fun n => 0<n ∧ ¬(∃ k, orbit k n=1))
    (Q := fun n => ¬(∃ k, orbit k n=1)) (fun _ h => h.2) N
  exact Nat.le_trans (failure_count_lower N hn) (Nat.mul_le_mul_left 8 hsub)

/-- No input zero or one meets even the first reciprocal-power target. -/
theorem all_powers_requires_large_start {n : Nat}
    (h : ∀ q, 0<q → BelowPower 1 q n) : 1<n := by
  obtain ⟨k, hk⟩ := h 1 (by decide)
  simp only [Nat.pow_one] at hk
  by_cases hz : n=0
  · subst n; omega
  · have hp := orbit_positive (by omega : 0<n) k
    omega

/-- The intersection over all positive reciprocal exponents is not density
one, although each member of this countable family is density one. -/
theorem not_density_one_all_powers :
    ¬DensityOne (fun n => ∀ q, 0<q → BelowPower 1 q n) := by
  intro h
  apply not_density_one_reaches_one
  apply densityOne_mono (P := fun n => ∀ q, 0<q → BelowPower 1 q n) _ h
  intro n hn
  exact (reaches_one_iff_all_powers (all_powers_requires_large_start hn)).mpr hn

/-- A concrete counterexample to interchanging the two quantifiers in a
power-threshold density argument. -/
theorem density_quantifiers_do_not_commute :
    (∀ q, 0<q → DensityOne (BelowPower 1 q)) ∧
    ¬DensityOne (fun n => ∀ q, 0<q → BelowPower 1 q n) :=
  ⟨fun q _ => below_power_density_one 1 q (by decide), not_density_one_all_powers⟩

end Collatz.DensityCountermodel.PowerComparison
