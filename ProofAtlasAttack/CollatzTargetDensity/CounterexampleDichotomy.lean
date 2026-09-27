import CollatzTargetDensity.AllTargets
import CollatzTargetDensity.OrbitInvariance

/-!
# Consequence of the all-target density theorem

It does not establish that the sparse-counterexample criterion holds.
-/
namespace CollatzTargetDensity
open Erdos1135
noncomputable section

/-- One counterexample would force a positive lower natural density of
    counterexamples. The density constant is not asserted to be uniform. -/
theorem counterexamples_positive_density (hbad : rawBad.Nonempty) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      c * (X : ℝ) ≤ (Terras.natCount rawBad X : ℝ) := by
  obtain ⟨n, hn⟩ := hbad
  obtain ⟨a, ha, hnot⟩ := bad_three_unit_of_bad hn
  obtain ⟨c, hc, X₀, hX₀⟩ := positive_density_all_targets ha
  refine ⟨c, hc, X₀, ?_⟩
  intro X hX
  have hmono := Terras.natCount_mono (rawReaches_subset_bad hnot) X
  exact (hX₀ X hX).trans (by exact_mod_cast hmono)

/-- The counterexample proportion becomes arbitrarily small along arbitrarily
    large cutoffs. This is a condition, not an established fact. -/
def SparseBadSubsequence : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ X₀ : ℕ, ∃ X : ℕ, X₀ ≤ X ∧ 0 < X ∧
    (Terras.natCount rawBad X : ℝ) < ε * (X : ℝ)

theorem collatz_iff_sparse_bad_subsequence :
    (∀ n : ℕ, 0 < n → Reaches n 1) ↔ SparseBadSubsequence := by
  constructor
  · intro hall ε hε X₀
    have hempty : rawBad = ∅ := by
      ext n
      constructor
      · intro hn
        exact False.elim (hn.2 (hall n hn.1))
      · intro hn
        exact False.elim hn
    let X := max X₀ 1
    have hXpos : 0 < X := by dsimp [X]; omega
    have hcount : Terras.natCount rawBad X = 0 := by
      rw [hempty]
      simp [Terras.natCount]
    refine ⟨X, le_max_left _ _, hXpos, ?_⟩
    rw [hcount, Nat.cast_zero]
    exact mul_pos hε (by exact_mod_cast hXpos)
  · intro hsparse n hn
    by_contra hnot
    obtain ⟨c, hc, X₀, hX₀⟩ := counterexamples_positive_density ⟨n, hn, hnot⟩
    obtain ⟨X, hX, _, hsmall⟩ := hsparse c hc X₀
    exact (not_lt_of_ge (hX₀ X hX)) hsmall

end
end CollatzTargetDensity
