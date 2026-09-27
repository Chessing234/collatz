import CollatzTargetDensity.HarmonicDensity
import CollatzTargetDensity.ProofChain

/-! Consequence for a hypothetical least counterexample and the remaining
quantitative gap. Neither lemma assumes that a counterexample exists. -/
namespace CollatzTargetDensity.HarmonicTargets
open Erdos1135 ProofChain Filter
open scoped Topology
noncomputable section

/-- Any least counterexample forces a reciprocal-size lower bound for its
avoidance tail, starting at a uniform quadratic cutoff. -/
theorem least_bad_forces_harmonic_tail :
    ∃ d : ℝ, 0 < d ∧ ∃ B : ℕ, 1 ≤ B ∧ ∀ m : ℕ, LeastBad m →
      ∀ X : ℕ, (B * m) ^ 2 ≤ X →
        d / m ≤ Tao.logCountingRatio (avoidsBelow m) X := by
  obtain ⟨d, hd, A, hA, hcount⟩ := uniform_raw_logCountingRatio_lower
  refine ⟨d / 4, by positivity, 4 * A, by omega, ?_⟩
  intro m hm X hX
  have hmpos : 0 < m := hm.1.1
  have hsize : 3 * m + 1 ≤ 4 * m := by omega
  have hbound : (A * (3 * m + 1)) ^ 2 ≤ X := by
    apply le_trans _ hX
    have hb : A * (3 * m + 1) ≤ 4 * A * m := by nlinarith
    exact Nat.pow_le_pow_left hb 2
  have hxpos : 0 < X := (by positivity : 0 < (A * (3 * m + 1)) ^ 2).trans_le hbound
  have hrat : (d / 4) / m ≤ d / (3 * m + 1 : ℕ) := by
    rw [div_div]
    apply div_le_div_of_nonneg_left hd.le (by positivity)
    exact_mod_cast hsize
  have hlo := hrat.trans (hcount (3 * m + 1) (by omega) X hbound)
  have hmono := div_le_div_of_nonneg_right
    (Tao.logCount_mono (successor_predecessors_avoid hm) X) (Tao.logMass_pos hxpos).le
  exact hlo.trans hmono

/-- Reciprocal-size lower bounds remain below every positive fixed inverse
power of log. Such a comparison does not supply the missing upper bound
for the actual avoidance set. -/
theorem reciprocal_eventually_lt_log_bound (p : ℕ) {d C : ℝ}
    (hd : 0 < d) (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop, d / m < C / (Real.log (m : ℝ)) ^ p := by
  have hs : ∀ᶠ x : ℝ in atTop, ‖Real.log x ^ p‖ ≤ (C / (2 * d)) * ‖x‖ :=
    Real.isLittleO_pow_log_id_atTop.bound (by positivity)
  have hsn := tendsto_natCast_atTop_atTop.eventually hs
  filter_upwards [hsn, eventually_ge_atTop 2] with m hs hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlpos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hppos : 0 < Real.log (m : ℝ) ^ p := pow_pos hlpos p
  have hh : Real.log (m : ℝ) ^ p ≤ C / (2 * d) * m := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hlpos.le, abs_of_nonneg hmpos.le] using hs
  apply (div_lt_div_iff₀ hmpos hppos).mpr
  have hh' := mul_le_mul_of_nonneg_left hh hd.le
  have he : d * (C / (2 * d) * m) = C * m / 2 := by field_simp
  rw [he] at hh'
  have hp : 0 < C * (m : ℝ) := mul_pos hC hmpos
  linarith

end
end CollatzTargetDensity.HarmonicTargets
