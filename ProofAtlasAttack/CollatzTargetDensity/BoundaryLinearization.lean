import CollatzTargetDensity.InverseBoundary

/-! Exact multiplicative coordinates on a hypothetical injective Syracuse orbit.
The coordinate uses the entire future orbit. Its existence is not a descent
argument or an effective way to decide convergence. -/
namespace CollatzTargetDensity.BoundaryLinearization
open Erdos1135 OrbitReciprocals InverseBoundary Filter
open scoped BigOperators Topology
noncomputable section

theorem orbit_shift (n k i : ℕ) : orbit (orbit n k) i = orbit n (i + k) := by
  exact (Function.iterate_add_apply _ i k n).symm

theorem injective_shift {n : ℕ} (hi : Function.Injective (orbit n)) (k : ℕ) :
    Function.Injective (orbit (orbit n k)) := by
  intro i j hij
  simp only [orbit_shift] at hij
  have := hi hij
  omega

theorem correction_shift (n k i : ℕ) : correction (orbit n k) i = correction n (i + k) := by
  simp only [correction, orbit_shift]

/-- Removing a finite prefix leaves precisely the correction at its endpoint. -/
theorem correction_split {n : ℕ} (hn : 0 < n) (hi : Function.Injective (orbit n))
    (k : ℕ) :
    correctionSum n k + (∑' i, correction (orbit n k) i) = ∑' i, correction n i := by
  simpa only [correctionSum, correction_shift] using
    (corrections_summable hn hi).sum_add_tsum_nat_add k

/-- The nonlinear +1 correction disappears in the boundary coordinate. -/
theorem boundary_transport {n : ℕ} (hn : 0 < n) (hi : Function.Injective (orbit n))
    (k : ℕ) : scale n k * realBoundary (orbit n k) = realBoundary n := by
  calc
    _ = remainder n k * Real.exp (∑' i, correction (orbit n k) i) := by
      unfold realBoundary remainder
      ring
    _ = (n : ℝ) * Real.exp (correctionSum n k) *
        Real.exp (∑' i, correction (orbit n k) i) := by
      rw [remainder_eq_exp_correction hn]
    _ = realBoundary n := by
      rw [mul_assoc, ← Real.exp_add, correction_split hn hi]
      rfl

/-- Exact one-step law: `2^a B(S n) = 3 B(n)`. -/
theorem boundary_step {n : ℕ} (hn : 0 < n) (hi : Function.Injective (orbit n)) :
    (2 : ℝ) ^ Tao.syracuseExponent n * realBoundary (Tao.syracuse n) =
      3 * realBoundary n := by
  have h := boundary_transport hn hi 1
  simp [scale, valuationTotal, orbit] at h
  linarith

/-- Far along the orbit, the exact coordinate has vanishing relative error.
No uniformity over starting values or absolute error bound is asserted. -/
theorem boundary_relative_tendsto_one {n : ℕ} (hn : 0 < n)
    (hi : Function.Injective (orbit n)) :
    Tendsto (fun k => realBoundary (orbit n k) / (orbit n k : ℝ)) atTop (nhds 1) := by
  have ht : Tendsto (fun k => ∑' i, correction n (i + k)) atTop (nhds 0) := by
    have h := (tendsto_const_nhds (x := ∑' i, correction n i)).sub
      (corrections_summable hn hi).hasSum.tendsto_sum_nat
    have he (k : ℕ) : (∑' i, correction n i) - correctionSum n k =
        ∑' i, correction n (i + k) := by
      have hs := correction_split hn hi k
      simp only [correction_shift] at hs
      linarith
    simpa only [sub_self, ← he, correctionSum] using h
  have h := Real.continuous_exp.tendsto (0 : ℝ) |>.comp ht
  have he (k : ℕ) : realBoundary (orbit n k) / (orbit n k : ℝ) =
      Real.exp (∑' i, correction n (i + k)) := by
    have hp : (orbit n k : ℝ) ≠ 0 := by exact_mod_cast (orbit_pos hn k).ne'
    simp only [realBoundary, correction_shift]
    field_simp
  simpa only [he, Real.exp_zero] using h

theorem boundary_gt_start {n : ℕ} (hn : 0 < n) (hi : Function.Injective (orbit n)) :
    (n : ℝ) < realBoundary n := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < correction n 0 := by
    apply Real.log_pos
    simp only [orbit, Function.iterate_zero, id_eq]
    have : (0 : ℝ) < 1 / (3 * (n : ℝ)) := by positivity
    linarith
  have ht := (corrections_summable hn hi).tsum_pos (correction_nonneg n) 0 hc
  have he : (1 : ℝ) < Real.exp (∑' i, correction n i) := by
    simpa using Real.exp_lt_exp.mpr ht
  simpa only [realBoundary, mul_one] using mul_lt_mul_of_pos_left he hp

/-- Relative error tends to zero, but absolute error stays above 1/3. -/
theorem boundary_absolute_gap {n : ℕ} (hn : 0 < n)
    (hi : Function.Injective (orbit n)) : (n : ℝ) + 1 / 3 < realBoundary n := by
  have hb := boundary_gt_start (orbit_pos hn 1) (injective_shift hi 1)
  have hm := mul_lt_mul_of_pos_left hb (scale_pos n 1)
  rw [boundary_transport hn hi 1] at hm
  have he : scale n 1 * (orbit n 1 : ℝ) = (n : ℝ) + 1 / 3 := by
    change remainder n 1 = _
    rw [remainder_eq_start_add_inverseSum]
    simp [inverseSum, scale, valuationTotal]
  rwa [he] at hm

/-- Asymptotic normalization uniquely determines the coordinate on an
injective orbit. This is rigidity, not a proof that such an orbit exists. -/
theorem boundary_unique {n : ℕ} (hn : 0 < n) (hi : Function.Injective (orbit n))
    (b : ℕ → ℝ) (htransport : ∀ k, scale n k * b k = b 0)
    (hnormal : Tendsto (fun k => b k / (orbit n k : ℝ)) atTop (nhds 1)) :
    b 0 = realBoundary n := by
  have h := (remainder_tendsto_realBoundary hn hi).mul hnormal
  have he (k : ℕ) : remainder n k * (b k / (orbit n k : ℝ)) = b 0 := by
    have hp : (orbit n k : ℝ) ≠ 0 := by exact_mod_cast (orbit_pos hn k).ne'
    calc
      _ = scale n k * b k := by unfold remainder; field_simp
      _ = b 0 := htransport k
  have hc : Tendsto (fun _ : ℕ => b 0) atTop (nhds (realBoundary n)) := by
    simpa only [he, mul_one] using h
  exact tendsto_nhds_unique tendsto_const_nhds hc

end
end CollatzTargetDensity.BoundaryLinearization
