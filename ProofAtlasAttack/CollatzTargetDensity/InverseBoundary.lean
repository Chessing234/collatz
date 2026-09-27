import CollatzTargetDensity.OrbitDiscrepancy

/-! The real inverse-affine boundary term. A positive boundary survives on
an injective positive orbit, so it cannot be dropped from the limiting identity. -/
namespace CollatzTargetDensity.InverseBoundary
open Erdos1135 OrbitReciprocals Filter
open scoped BigOperators Topology
noncomputable section

def scale (n k : ℕ) : ℝ := (2 : ℝ) ^ valuationTotal n k / (3 : ℝ) ^ k

def remainder (n k : ℕ) : ℝ := scale n k * (orbit n k : ℝ)

def inverseSum (n k : ℕ) : ℝ := ∑ i ∈ Finset.range k, scale n i / 3

theorem scale_pos (n k : ℕ) : 0 < scale n k := by unfold scale; positivity

theorem scale_succ (n k : ℕ) :
    scale n (k + 1) = scale n k * (2 : ℝ) ^ Tao.syracuseExponent (orbit n k) / 3 := by
  simp only [scale, valuationTotal, Finset.sum_range_succ, pow_add, pow_succ]
  ring

/-- The actual endpoint identity, with the remainder retained. -/
theorem remainder_succ (n k : ℕ) :
    remainder n (k + 1) = remainder n k + scale n k / 3 := by
  have he : (2 : ℝ) ^ Tao.syracuseExponent (orbit n k) * (orbit n (k + 1) : ℝ) =
      3 * (orbit n k : ℝ) + 1 := by
    have h := Tao.two_pow_syracuseExponent_mul_syracuse (orbit n k)
    rw [orbit_succ] at h
    exact_mod_cast h
  unfold remainder
  rw [scale_succ]
  calc
    _ = scale n k / 3 * ((2 : ℝ) ^ Tao.syracuseExponent (orbit n k) * orbit n (k + 1)) := by ring
    _ = scale n k / 3 * (3 * (orbit n k : ℝ) + 1) := by rw [he]
    _ = _ := by ring

theorem remainder_eq_start_add_inverseSum (n k : ℕ) :
    remainder n k = (n : ℝ) + inverseSum n k := by
  induction k with
  | zero => simp [remainder, scale, valuationTotal, inverseSum, orbit]
  | succ k ih => rw [remainder_succ, ih]; simp [inverseSum, Finset.sum_range_succ, add_assoc]

theorem inverseSum_nonneg (n k : ℕ) : 0 ≤ inverseSum n k := by
  exact Finset.sum_nonneg (fun i _ => (div_pos (scale_pos n i) (by norm_num)).le)

theorem remainder_ge_start (n k : ℕ) : (n : ℝ) ≤ remainder n k := by
  rw [remainder_eq_start_add_inverseSum]
  exact le_add_of_nonneg_right (inverseSum_nonneg n k)

theorem log_scale (n k : ℕ) : Real.log (scale n k) = -discrepancy n k := by
  unfold scale discrepancy
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  ring

theorem scale_eq_exp (n k : ℕ) : scale n k = Real.exp (-discrepancy n k) := by
  rw [← log_scale, Real.exp_log (scale_pos n k)]

/-- The boundary equals the start times the exact nonlinear correction product. -/
theorem remainder_eq_exp_correction {n : ℕ} (hn : 0 < n) (k : ℕ) :
    remainder n k = (n : ℝ) * Real.exp (correctionSum n k) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : (0 : ℝ) < orbit n k := by exact_mod_cast orbit_pos hn k
  have he := log_orbit_identity hn k
  have hlog : Real.log (remainder n k) = Real.log n + correctionSum n k := by
    rw [remainder, Real.log_mul (scale_pos n k).ne' ha.ne', log_scale, he]
    ring
  have hp : 0 < remainder n k := mul_pos (scale_pos n k) ha
  rw [← Real.exp_log hp, hlog, Real.exp_add, Real.exp_log hnR]

def realBoundary (n : ℕ) : ℝ := (n : ℝ) * Real.exp (∑' i, correction n i)

theorem realBoundary_pos {n : ℕ} (hn : 0 < n) : 0 < realBoundary n := by
  unfold realBoundary
  positivity

/-- On an injective orbit the real boundary converges to a strictly positive value. -/
theorem remainder_tendsto_realBoundary {n : ℕ} (hn : 0 < n)
    (hi : Function.Injective (orbit n)) :
    Tendsto (remainder n) atTop (nhds (realBoundary n)) := by
  have hc : Tendsto (correctionSum n) atTop (nhds (∑' i, correction n i)) :=
    (corrections_summable hn hi).hasSum.tendsto_sum_nat
  have h : Tendsto (fun k => (n : ℝ) * Real.exp (correctionSum n k)) atTop
      (nhds ((n : ℝ) * Real.exp (∑' i, correction n i))) :=
    tendsto_const_nhds.mul (Real.continuous_exp.tendsto _ |>.comp hc)
  simpa only [← remainder_eq_exp_correction hn, realBoundary] using h

theorem uniform_remainder_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → Function.Injective (orbit n) →
      ∀ k : ℕ, remainder n k ≤ (n : ℝ) * C := by
  obtain ⟨C, hC, hbound⟩ := uniform_correctionSum_bound
  refine ⟨Real.exp C, Real.exp_pos _, ?_⟩
  intro n hn hi k
  rw [remainder_eq_exp_correction hn]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hbound n hn hi k).2) (by positivity)

/-- The positive inverse-affine series converges in the real topology. -/
theorem inverse_terms_summable {n : ℕ} (hn : 0 < n)
    (hi : Function.Injective (orbit n)) : Summable (fun k => scale n k / 3) := by
  obtain ⟨C, _, hbound⟩ := uniform_remainder_bound
  apply summable_of_sum_range_le (fun k => (div_pos (scale_pos n k) (by norm_num)).le)
  intro k
  have he := remainder_eq_start_add_inverseSum n k
  have hb := hbound n hn hi k
  change inverseSum n k ≤ (n : ℝ) * C
  have hnon : (0 : ℝ) ≤ n := by positivity
  linarith

theorem inverseSum_tendsto {n : ℕ} (hn : 0 < n) (hi : Function.Injective (orbit n)) :
    Tendsto (inverseSum n) atTop (nhds (realBoundary n - n)) := by
  have h := (remainder_tendsto_realBoundary hn hi).sub_const (n : ℝ)
  simpa only [remainder_eq_start_add_inverseSum, add_sub_cancel_left] using h

theorem inverse_real_tsum {n : ℕ} (hn : 0 < n) (hi : Function.Injective (orbit n)) :
    (∑' k, scale n k / 3) = realBoundary n - n := by
  exact tendsto_nhds_unique (inverse_terms_summable hn hi).hasSum.tendsto_sum_nat
    (inverseSum_tendsto hn hi)

theorem remainder_not_tendsto_zero {n : ℕ} (hn : 0 < n) :
    ¬Tendsto (remainder n) atTop (nhds 0) := by
  intro h
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsmall := (tendsto_order.mp h).2 (n : ℝ) hpos
  obtain ⟨k, hk⟩ := hsmall.exists
  exact (not_lt_of_ge (remainder_ge_start n k)) hk

end
end CollatzTargetDensity.InverseBoundary
