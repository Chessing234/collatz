import CollatzTargetDensity.SyracuseMinorant

/-!
# All-generation one-sided core comparison

This compares the literal imported backward core marks with the actual
finite Syracuse densities. No positivity of the limiting core or uniform
Syracuse floor is assumed or asserted here.
-/

namespace CollatzTargetDensity.SyracuseMinorant
open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators
noncomputable section

theorem mean_positive_triangle (q : ℕ) (f g h : ZMod (3 ^ q) → ℝ) :
    ndTernaryUniformMean q (fun y => max (f y - h y) 0) ≤
      ndTernaryUniformMean q (fun y => max (f y - g y) 0) +
        ndTernaryUniformMean q (fun y => max (g y - h y) 0) := by
  unfold ndTernaryUniformMean
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by unfold ndTernaryUniformScale; positivity)
  apply Finset.sum_le_sum
  intro y _
  apply max_le
  · have h1 := le_max_left (f y - g y) 0
    have h2 := le_max_left (g y - h y) 0
    linarith
  · exact add_nonneg (le_max_right _ _) (le_max_right _ _)

theorem core_word_filter_bounds (b m : ℕ) (w : List ℕ+) :
    0 ≤ ndRootCoreWordFilter b m w ∧ ndRootCoreWordFilter b m w ≤ 1 := by
  unfold ndRootCoreWordFilter
  split_ifs <;> norm_num

/-- The error depends on generation and terminal conductor, but not on the
root, initial floor, cap schedule, strip widths, or backward horizon. -/
theorem backward_mark_positive_error_polynomial (A : ℕ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : ℕ) (cap width : ℕ → ℕ) (k n : ℕ), 1 ≤ k →
      ndTernaryUniformMean (ndRootCoreBackwardConductor b k n) (fun y =>
        max (ndRootCoreBackwardMark b cap width k n y -
          ndSyracuseUnitReferenceDensity (ndRootCoreBackwardConductor b k n) y) 0) ≤
        (n : ℝ) * (C / (k : ℝ) ^ A) := by
  obtain ⟨C, hC, hrate⟩ := filtered_kernel_positive_error_polynomial A hA
  refine ⟨C, hC, ?_⟩
  intro b cap width k n hk
  induction n generalizing b cap with
  | zero =>
    simp [ndRootCoreBackwardConductor, ndRootCoreBackwardMark,
      ndTernaryUniformMean]
  | succ n ih =>
    let b' := b + b / 100
    let q := ndRootCoreBackwardConductor b' k n
    let tail := ndRootCoreBackwardMark b' (ndGeom2RootSideCapTail cap) width k n
    let psi := ndRootCoreWordFilter b (width b)
    let K := ndRootCoreFilteredKernel b (ndGeom2ShiftedWideSymmetricShiftRadius b) (cap 0) q psi
    have hq : k ≤ q := rootCoreBackwardConductor_ge b' k n
    have hqpos : 1 ≤ q := hk.trans hq
    have hp : ∀ w, 0 ≤ psi w ∧ psi w ≤ 1 := core_word_filter_bounds b (width b)
    have hcontract := filtered_kernel_positive_contraction b
      (ndGeom2ShiftedWideSymmetricShiftRadius b) (cap 0) q psi hp
      tail (ndSyracuseUnitReferenceDensity q)
    have hstep := hrate b (ndGeom2ShiftedWideSymmetricShiftRadius b) (cap 0) q hqpos psi
      (fun w => (hp w).2)
    have htri := mean_positive_triangle (ndGeom2ShiftedWideSymmetricHorizon b + q)
      (K tail) (K (ndSyracuseUnitReferenceDensity q))
      (ndSyracuseUnitReferenceDensity (ndGeom2ShiftedWideSymmetricHorizon b + q))
    have hprev := ih b' (ndGeom2RootSideCapTail cap)
    have hden : C / (q : ℝ) ^ A ≤ C / (k : ℝ) ^ A := by
      apply div_le_div_of_nonneg_left hC (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hq) A
    change ndTernaryUniformMean (ndGeom2ShiftedWideSymmetricHorizon b + q) (fun y =>
      max (K tail y - ndSyracuseUnitReferenceDensity
        (ndGeom2ShiftedWideSymmetricHorizon b + q) y) 0) ≤ _
    change ndTernaryUniformMean q (fun y =>
      max (tail y - ndSyracuseUnitReferenceDensity q y) 0) ≤ _ at hprev
    change ndTernaryUniformMean (ndGeom2ShiftedWideSymmetricHorizon b + q) (fun y =>
      max (K tail y - K (ndSyracuseUnitReferenceDensity q) y) 0) ≤ _ at hcontract
    change ndTernaryUniformMean (ndGeom2ShiftedWideSymmetricHorizon b + q) (fun y =>
      max (K (ndSyracuseUnitReferenceDensity q) y -
        ndSyracuseUnitReferenceDensity (ndGeom2ShiftedWideSymmetricHorizon b + q) y) 0) ≤ _ at hstep
    push_cast
    nlinarith

end
end CollatzTargetDensity.SyracuseMinorant
