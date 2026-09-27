import Erdos1135.Terras.Core.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
Checks on counting-measure time averages for the actual shortcut Collatz map.
Known powers-of-two orbits already preclude a starting-set-independent mean
bound and a summable limit for every summable observable. No assertion about
unknown Collatz orbits or about other finite measures is made here.
-/
namespace CollatzTargetDensity.CountingMeasureCheck
open Erdos1135 Filter
open scoped BigOperators Topology
noncomputable section

def cycleIndicator (x : ℕ) : ℝ := if x = 1 ∨ x = 2 then 1 else 0

def visitMean (N x : ℕ) : ℝ :=
  (∑ j ∈ Finset.range N, cycleIndicator ((Terras.accelerated^[j + 1]) x)) / N

def ensembleMean (Y : Finset ℕ) (N : ℕ) : ℝ := ∑ x ∈ Y, visitMean N x

theorem cycle_forward (j : ℕ) {x : ℕ} (hx : x = 1 ∨ x = 2) :
    (Terras.accelerated^[j]) x = 1 ∨ (Terras.accelerated^[j]) x = 2 := by
  induction j with
  | zero => exact hx
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h <;> rw [h] <;> norm_num [Terras.accelerated]

theorem accelerated_pow_two_succ (k : ℕ) :
    Terras.accelerated (2 ^ (k + 1)) = 2 ^ k := by
  have he : Even (2 ^ (k + 1)) := ⟨2 ^ k, by rw [pow_succ]; omega⟩
  rw [Terras.accelerated_eq_div_two_of_even he, pow_succ, Nat.mul_div_left]
  norm_num

theorem iterate_pow_two (k : ℕ) : (Terras.accelerated^[k]) (2 ^ k) = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, accelerated_pow_two_succ, ih]

theorem cycleIndicator_pow_two_eventually (k j : ℕ) (hj : k ≤ j + 1) :
    cycleIndicator ((Terras.accelerated^[j + 1]) (2 ^ k)) = 1 := by
  have he : j + 1 = (j + 1 - k) + k := by omega
  rw [he, Function.iterate_add_apply, iterate_pow_two]
  rcases cycle_forward (j + 1 - k) (Or.inl rfl) with h | h <;> simp [cycleIndicator, h]

/-- An elementary Cesaro calculation, retaining the finite initial segment. -/
theorem mean_tendsto_of_eventually_eq (f : ℕ → ℝ) (a : ℝ) (k : ℕ)
    (hf : ∀ j, k ≤ j → f j = a) :
    Tendsto (fun N : ℕ => (∑ j ∈ Finset.range N, f j) / N) atTop (𝓝 a) := by
  let B := (∑ j ∈ Finset.range k, f j) - (k : ℝ) * a
  have hdiv : Tendsto (fun N : ℕ => B / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => a + B / (N : ℝ)) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.add hdiv
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop k, eventually_ge_atTop 1] with N hN hpos
  have hsum : (∑ j ∈ Finset.range N, f j) =
      (∑ j ∈ Finset.range k, f j) + (N - k : ℕ) * a := by
    rw [show N = k + (N - k) by omega, Finset.sum_range_add]
    simp [hf]
  have hNzero : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [hsum, Nat.cast_sub hN]
  dsimp [B]
  field_simp
  ring

theorem visitMean_pow_two_tendsto (k : ℕ) :
    Tendsto (fun N => visitMean N (2 ^ k)) atTop (𝓝 1) := by
  exact mean_tendsto_of_eventually_eq _ 1 k
    (fun j hj => cycleIndicator_pow_two_eventually k j (by omega))

theorem cycleIndicator_summable : Summable cycleIndicator := by
  apply summable_of_ne_finset_zero (s := {1, 2})
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  simp [cycleIndicator, hx.1, hx.2]

/-- Every possible pointwise time-average limit of this summable observable
is non-summable. Powers of two alone force infinitely many values equal to 1. -/
theorem no_summable_visitMean_limit :
    ¬ ∃ g : ℕ → ℝ, Summable g ∧
      ∀ x : ℕ, 0 < x → Tendsto (fun N => visitMean N x) atTop (𝓝 (g x)) := by
  rintro ⟨g, hg, hlim⟩
  have hpow (k : ℕ) : g (2 ^ k) = 1 :=
    tendsto_nhds_unique (hlim _ (by positivity)) (visitMean_pow_two_tendsto k)
  have hs : Summable (fun k : ℕ => g (2 ^ k)) :=
    hg.comp_injective (Nat.pow_right_injective (by decide : 2 ≤ 2))
  simp_rw [hpow] at hs
  rw [summable_const_iff] at hs
  norm_num at hs

theorem cycleIndicator_integrable_count :
    MeasureTheory.Integrable cycleIndicator MeasureTheory.Measure.count := by
  apply MeasureTheory.integrable_count_iff.mpr
  apply summable_of_ne_finset_zero (s := {1, 2})
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  simp [cycleIndicator, hx.1, hx.2]

/-- Literal counting-measure L1 formulation. The requirement on limits is
only for positive starts, so adjoining zero to the formal domain is immaterial. -/
theorem no_integrable_visitMean_limit :
    ¬ ∃ g : ℕ → ℝ, MeasureTheory.Integrable g MeasureTheory.Measure.count ∧
      ∀ x : ℕ, 0 < x → Tendsto (fun N => visitMean N x) atTop (𝓝 (g x)) := by
  rintro ⟨g, hg, hlim⟩
  exact no_summable_visitMean_limit
    ⟨g, (MeasureTheory.integrable_count_iff.mp hg).of_norm, hlim⟩

def powerSeeds (r : ℕ) : Finset ℕ := (Finset.range (r + 1)).image (fun k => 2 ^ k)

theorem powerSeeds_positive (r : ℕ) : ∀ x ∈ powerSeeds r, 0 < x := by
  intro x hx
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
  positivity

theorem ensembleMean_powerSeeds_tendsto (r : ℕ) :
    Tendsto (ensembleMean (powerSeeds r)) atTop (𝓝 ((r : ℝ) + 1)) := by
  have he (N : ℕ) : ensembleMean (powerSeeds r) N =
      ∑ k ∈ Finset.range (r + 1), visitMean N (2 ^ k) := by
    unfold ensembleMean powerSeeds
    rw [Finset.sum_image]
    exact fun a _ b _ h => Nat.pow_right_injective (by decide : 2 ≤ 2) h
  simp_rw [funext he]
  have h := tendsto_finset_sum (Finset.range (r + 1)) (fun k _ => visitMean_pow_two_tendsto k)
  simpa using h

/-- No finite constant works uniformly over all finite positive starting sets,
even when the target set is fixed to the known two-cycle {1,2}. -/
theorem no_uniform_counting_mean_bound :
    ¬ ∃ C : ℝ, ∀ Y : Finset ℕ, (∀ x ∈ Y, 0 < x) →
      limsup (ensembleMean Y) atTop ≤ C * 2 := by
  rintro ⟨C, hC⟩
  obtain ⟨r, hr⟩ := exists_nat_gt (2 * C)
  have hbound := hC (powerSeeds r) (powerSeeds_positive r)
  rw [(ensembleMean_powerSeeds_tendsto r).limsup_eq] at hbound
  linarith

theorem ensembleMean_three_seeds (N : ℕ) (hN : 0 < N) :
    ensembleMean {1, 2, 4} N = 3 := by
  have hx (x : ℕ) (h : x = 1 ∨ x = 2 ∨ x = 4) : visitMean N x = 1 := by
    have hg (j : ℕ) : cycleIndicator ((Terras.accelerated^[j + 1]) x) = 1 := by
      rw [Function.iterate_succ_apply]
      have hfirst : Terras.accelerated x = 1 ∨ Terras.accelerated x = 2 := by
        rcases h with rfl | rfl | rfl <;> norm_num [Terras.accelerated]
      rcases cycle_forward j hfirst with hh | hh <;> simp [cycleIndicator, hh]
    unfold visitMean
    simp_rw [hg]
    simp [Nat.ne_of_gt hN]
  norm_num [ensembleMean, hx 1 (by simp), hx 2 (by simp), hx 4 (by simp)]

end
end CollatzTargetDensity.CountingMeasureCheck
