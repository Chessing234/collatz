import CollatzTargetDensity.AllTargets
import CollatzTargetDensity.ThreeDivisible

/-! Literal map and count interface for the all-target density extension. -/
namespace CollatzTargetDensity

def step (n : ℕ) : ℕ := if Even n then n / 2 else 3 * n + 1

def reachesTarget (target n : ℕ) : Prop :=
  0 < n ∧ ∃ k : ℕ, (step^[k]) n = target

open Classical in
noncomputable def countBelow (target X : ℕ) : ℕ :=
  Nat.count (reachesTarget target) X

/-- The count uses positive starting integers strictly below X and the
    ordinary Collatz map. The lower-density constant may depend on target. -/
theorem positive_density (target : ℕ) (_hpos : 0 < target) (hthree : target % 3 ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      c * (X : ℝ) ≤ (countBelow target X : ℝ) := by
  exact positive_density_all_targets hthree

theorem positive_density_iff (target : ℕ) (hpos : 0 < target) :
    (∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      c * (X : ℝ) ≤ (countBelow target X : ℝ)) ↔ target % 3 ≠ 0 := by
  constructor
  · intro h hthree
    exact no_positive_lower_density_three_divisible hpos hthree h
  · exact positive_density target hpos

end CollatzTargetDensity
