import CollatzTargetDensity.ShadowOscillation

/-! A bounded shadow would force uniform exponential escape. This is a
conditional restriction on divergence, not an exclusion of exponential escape. -/
namespace CollatzTargetDensity.ShadowGrowth
open Erdos1135 OrbitReciprocals InverseBoundary BoundaryLinearization ShadowOscillation
open scoped BigOperators
noncomputable section

def tailBudget (n k : ℕ) : ℝ := scale n k * shadow (orbit n k)

theorem tailBudget_eq {n : ℕ} (hn : 0 < n) (hi : Function.Injective (orbit n))
    (k : ℕ) : tailBudget n k = realBoundary n - remainder n k := by
  unfold tailBudget shadow remainder
  rw [mul_sub, boundary_transport hn hi]

theorem tailBudget_succ {n : ℕ} (hn : 0 < n) (hi : Function.Injective (orbit n))
    (k : ℕ) : tailBudget n (k + 1) = tailBudget n k - scale n k / 3 := by
  rw [tailBudget_eq hn hi, tailBudget_eq hn hi, remainder_succ]
  ring

theorem scale_le_tailBudget {n : ℕ} (hn : Odd n) (hi : Function.Injective (orbit n))
    (k : ℕ) : scale n k ≤ tailBudget n k := by
  have h := shadow_ge_one (orbit_odd hn k) (injective_shift hi k)
  simpa only [mul_one, tailBudget] using mul_le_mul_of_nonneg_left h (scale_pos n k).le

/-- A bound at all orbit points supplies a geometric contraction of the
remaining inverse-series budget. -/
theorem tailBudget_geometric {n : ℕ} (hn : Odd n) (hi : Function.Injective (orbit n))
    {M : ℝ} (hM : 1 ≤ M) (hbound : ∀ k, shadow (orbit n k) ≤ M) (k : ℕ) :
    tailBudget n k ≤ ((3 * M - 1) / (3 * M)) ^ k * shadow n := by
  have hMp : 0 < 3 * M := by linarith
  have hr : 0 ≤ (3 * M - 1) / (3 * M) := div_nonneg (by linarith) hMp.le
  have hstep (j : ℕ) : tailBudget n (j + 1) ≤
      ((3 * M - 1) / (3 * M)) * tailBudget n j := by
    have hb : tailBudget n j ≤ scale n j * M :=
      mul_le_mul_of_nonneg_left (hbound j) (scale_pos n j).le
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hMp).2
    rw [tailBudget_succ hn.pos hi]
    nlinarith
  induction k with
  | zero => simp [tailBudget, scale, valuationTotal, orbit]
  | succ k ih =>
    calc
      _ ≤ ((3 * M - 1) / (3 * M)) * tailBudget n k := hstep k
      _ ≤ ((3 * M - 1) / (3 * M)) *
          (((3 * M - 1) / (3 * M)) ^ k * shadow n) :=
        mul_le_mul_of_nonneg_left ih hr
      _ = _ := by ring

/-- Explicit exponential lower bound, stated without logarithms or division
by orbit values: the factor `(3M-1)/(3M)` lies strictly between zero and one. -/
theorem bounded_shadow_forces_growth {n : ℕ} (hn : Odd n)
    (hi : Function.Injective (orbit n)) {M : ℝ} (hM : 1 ≤ M)
    (hbound : ∀ k, shadow (orbit n k) ≤ M) (k : ℕ) :
    (n : ℝ) ≤ M * ((3 * M - 1) / (3 * M)) ^ k * (orbit n k : ℝ) := by
  have hs := (scale_le_tailBudget hn hi k).trans (tailBudget_geometric hn hi hM hbound k)
  have hzero : shadow n ≤ M := by simpa [orbit] using hbound 0
  have hpow : 0 ≤ ((3 * M - 1) / (3 * M)) ^ k :=
    pow_nonneg (div_nonneg (by linarith) (by linarith)) k
  have hs' : scale n k ≤ M * ((3 * M - 1) / (3 * M)) ^ k := by
    calc
      _ ≤ ((3 * M - 1) / (3 * M)) ^ k * shadow n := hs
      _ ≤ ((3 * M - 1) / (3 * M)) ^ k * M := mul_le_mul_of_nonneg_left hzero hpow
      _ = _ := mul_comm _ _
  exact (remainder_ge_start n k).trans
    (mul_le_mul_of_nonneg_right hs' (by positivity : (0 : ℝ) ≤ orbit n k))

end
end CollatzTargetDensity.ShadowGrowth
