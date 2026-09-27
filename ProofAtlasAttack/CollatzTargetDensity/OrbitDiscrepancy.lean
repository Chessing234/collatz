import CollatzTargetDensity.OrbitReciprocals

/-! The exact additive drift of a hypothetical divergent Syracuse trajectory.
Bounded nonlinear corrections imply drift to positive infinity, not a contradiction. -/
namespace CollatzTargetDensity.OrbitReciprocals
open Erdos1135 Filter
open scoped BigOperators Topology
noncomputable section

def valuationTotal (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, Tao.syracuseExponent (orbit n i)

def discrepancy (n k : ℕ) : ℝ :=
  (k : ℝ) * Real.log 3 - (valuationTotal n k : ℝ) * Real.log 2

def correction (n i : ℕ) : ℝ :=
  Real.log (1 + 1 / (3 * (orbit n i : ℝ)))

def correctionSum (n k : ℕ) : ℝ := ∑ i ∈ Finset.range k, correction n i

theorem correction_nonneg (n i : ℕ) : 0 ≤ correction n i := by
  apply Real.log_nonneg
  have h : (0 : ℝ) ≤ 1 / (3 * (orbit n i : ℝ)) := by positivity
  linarith

theorem correction_le (n i : ℕ) : correction n i ≤ 1 / (3 * (orbit n i : ℝ)) := by
  have hp : (0 : ℝ) ≤ 1 / (3 * (orbit n i : ℝ)) := by positivity
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (3 * (orbit n i : ℝ)) by linarith)
  simpa [correction] using h

/-- Exact logarithmic form of one Syracuse step. -/
theorem log_orbit_step {n : ℕ} (hn : 0 < n) (i : ℕ) :
    Real.log (orbit n (i + 1) : ℝ) = Real.log (orbit n i : ℝ) + Real.log 3 -
      (Tao.syracuseExponent (orbit n i) : ℝ) * Real.log 2 + correction n i := by
  have ha : (0 : ℝ) < orbit n i := by exact_mod_cast orbit_pos hn i
  have hb : (0 : ℝ) < orbit n (i + 1) := by exact_mod_cast orbit_pos hn (i + 1)
  have he : (2 : ℝ) ^ Tao.syracuseExponent (orbit n i) * orbit n (i + 1) =
      3 * (orbit n i : ℝ) + 1 := by
    have h := Tao.two_pow_syracuseExponent_mul_syracuse (orbit n i)
    rw [orbit_succ] at h
    exact_mod_cast h
  have he' : 3 * (orbit n i : ℝ) + 1 =
      (3 * (orbit n i : ℝ)) * (1 + 1 / (3 * (orbit n i : ℝ))) := by field_simp
  have hh := congrArg Real.log he
  rw [Real.log_mul (by positivity) hb.ne', Real.log_pow, he',
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) ha.ne'] at hh
  unfold correction
  linarith

/-- Telescope without discarding the positive +1 corrections. -/
theorem log_orbit_identity {n : ℕ} (hn : 0 < n) (k : ℕ) :
    Real.log (orbit n k : ℝ) = Real.log n + discrepancy n k + correctionSum n k := by
  induction k with
  | zero => simp [orbit, discrepancy, valuationTotal, correctionSum]
  | succ k ih =>
    rw [log_orbit_step hn k, ih]
    simp only [discrepancy, valuationTotal, correctionSum, Finset.sum_range_succ,
      Nat.cast_add, Nat.cast_one]
    ring

/-- The accumulated nonlinear correction is bounded by one absolute constant
on every positive injective Syracuse trajectory. -/
theorem uniform_correctionSum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → Function.Injective (orbit n) →
      ∀ k : ℕ, 0 ≤ correctionSum n k ∧ correctionSum n k ≤ C := by
  obtain ⟨C, hC, hbound⟩ := uniform_orbit_reciprocal_bound
  refine ⟨C / 3, by positivity, ?_⟩
  intro n hn hi k
  constructor
  · exact Finset.sum_nonneg (fun i _ => correction_nonneg n i)
  · calc
      _ ≤ ∑ i ∈ Finset.range k, 1 / (3 * (orbit n i : ℝ)) :=
        Finset.sum_le_sum (fun i _ => correction_le n i)
      _ = (∑ i ∈ Finset.range k, 1 / (orbit n i : ℝ)) / 3 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ C / 3 := div_le_div_of_nonneg_right (hbound n hn hi _) (by norm_num)

theorem corrections_summable {n : ℕ} (hn : 0 < n) (hi : Function.Injective (orbit n)) :
    Summable (correction n) := by
  obtain ⟨C, _, hbound⟩ := uniform_correctionSum_bound
  exact summable_of_sum_range_le (correction_nonneg n) (fun k => (hbound n hn hi k).2)

/-- A nonrepeating positive Syracuse orbit must have additive valuation
discrepancy tending to +infinity. No claim of impossibility is made. -/
theorem discrepancy_tendsto_atTop {n : ℕ} (hn : 0 < n) (hi : Function.Injective (orbit n)) :
    Tendsto (discrepancy n) atTop atTop := by
  obtain ⟨C, _, hbound⟩ := uniform_correctionSum_bound
  have hlog : Tendsto (fun k => Real.log (orbit n k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hi.nat_tendsto_atTop)
  have hlower : ∀ k, Real.log (orbit n k : ℝ) - (Real.log n + C) ≤ discrepancy n k := by
    intro k
    have he := log_orbit_identity hn k
    have hb := (hbound n hn hi k).2
    linarith
  apply tendsto_atTop.2
  intro b
  filter_upwards [(tendsto_atTop.1 hlog) (b + Real.log n + C)] with k hk
  have h := hlower k
  linarith

end
end CollatzTargetDensity.OrbitReciprocals
