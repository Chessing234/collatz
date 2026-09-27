import CollatzTargetDensity.ArithmeticSeeds
import CollatzTargetDensity.Assembly
import CollatzTargetDensity.RawBridge

/-!+# Proposed all-target predecessor density endpoint

This file must pass the complete build and an axiom audit before its theorem
is reported as verified. The new argument depends on the imported analytic
machinery of Lech Mazur's positive-density theorem.
-/

namespace CollatzTargetDensity
open Erdos1135 Filter
noncomputable section

theorem positive_density_odd_target {target : ℕ}
    (hodd : Odd target) (hthree : target % 3 ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      c * (X : ℝ) ≤ (Terras.natCount (oddReaches target) X : ℝ) :=
  positive_density_of_seed_supply (seed_supply hodd hthree)

/-- Every positive target prime to 3 has a predecessor set of positive lower
    natural density. This is not a statement that every integer reaches 1. -/
theorem positive_density_all_targets {target : ℕ} (hthree : target % 3 ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      c * (X : ℝ) ≤ (Terras.natCount (rawReaches target) X : ℝ) := by
  obtain ⟨seed, hodd, hunit, hhit⟩ := exists_fertile_raw_child hthree
  obtain ⟨c, hc, hcount⟩ := positive_density_odd_target hodd hunit
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hcount
  refine ⟨c, hc, X₀, ?_⟩
  intro X hX
  have hmono := Terras.natCount_mono (oddReaches_subset_rawReaches hhit) X
  exact (hX₀ X hX).trans (by exact_mod_cast hmono)

end
end CollatzTargetDensity
