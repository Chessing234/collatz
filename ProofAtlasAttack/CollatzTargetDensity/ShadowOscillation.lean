import CollatzTargetDensity.BoundaryLinearization
import CollatzTargetDensity.PadicInverseBoundary
import CollatzTargetDensity.ValuationRecurrence

/-! A quantitative obstruction to replacing the exact multiplicative boundary
coordinate by an integer plus an asymptotically constant correction.
All shadow assertions concern hypothetical injective positive integer orbits. -/
namespace CollatzTargetDensity.ShadowOscillation
open Erdos1135 OrbitReciprocals InverseBoundary BoundaryLinearization Filter
open scoped BigOperators Topology
noncomputable section

def shadow (n : ℕ) : ℝ := realBoundary n - n

theorem shadow_step {n : ℕ} (hn : 0 < n) (hi : Function.Injective (orbit n)) :
    (2 : ℝ) ^ Tao.syracuseExponent n * shadow (Tao.syracuse n) = 3 * shadow n - 1 := by
  have hb := boundary_step hn hi
  have hs : (2 : ℝ) ^ Tao.syracuseExponent n * (Tao.syracuse n : ℝ) = 3 * (n : ℝ) + 1 := by
    exact_mod_cast Tao.two_pow_syracuseExponent_mul_syracuse n
  unfold shadow
  nlinarith

/-- The inverse series dominates the geometric series with ratio 2/3. -/
theorem shadow_ge_one {n : ℕ} (hn : Odd n) (hi : Function.Injective (orbit n)) :
    1 ≤ shadow n := by
  have hg : HasSum (fun k : ℕ => (2 / 3 : ℝ) ^ k / 3) 1 := by
    convert (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
      (by norm_num : (2 / 3 : ℝ) < 1)).div_const 3 using 1
    norm_num
  have hterm (k : ℕ) : (2 / 3 : ℝ) ^ k / 3 ≤ scale n k / 3 := by
    have hp : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ valuationTotal n k :=
      pow_le_pow_right₀ (by norm_num) (valuationTotal_ge_steps hn k)
    have hd := div_le_div_of_nonneg_right hp (by positivity : (0 : ℝ) ≤ 3 ^ k)
    simpa only [div_pow, scale] using
      div_le_div_of_nonneg_right hd (by norm_num : (0 : ℝ) ≤ 3)
  have h := hg.summable.tsum_le_tsum hterm (inverse_terms_summable hn.pos hi)
  rw [hg.tsum_eq, inverse_real_tsum hn.pos hi] at h
  exact h

/-- Every valuation at least two forces a downward jump of at least 2/3
in the shadow, although the relative coordinate error tends to zero. -/
theorem shadow_drop {n : ℕ} (hn : Odd n) (hi : Function.Injective (orbit n))
    (ha : 2 ≤ Tao.syracuseExponent n) :
    2 / 3 ≤ shadow n - shadow (Tao.syracuse n) := by
  have hnext : 1 ≤ shadow (Tao.syracuse n) := by
    simpa only [orbit, Function.iterate_one] using
      shadow_ge_one (orbit_odd hn 1) (injective_shift hi 1)
  have hp : (4 : ℝ) ≤ (2 : ℝ) ^ Tao.syracuseExponent n := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ha
    norm_num at h
    exact h
  have hm := mul_le_mul_of_nonneg_right hp (by linarith : 0 ≤ shadow (Tao.syracuse n))
  have hs := shadow_step hn.pos hi
  nlinarith

/-- The jump obstruction occurs in every tail, not just at one special step. -/
theorem arbitrarily_late_drop {n : ℕ} (hn : Odd n) (hi : Function.Injective (orbit n))
    (N : ℕ) : ∃ k ≥ N, 2 / 3 ≤ shadow (orbit n k) - shadow (orbit n (k + 1)) := by
  obtain ⟨k, hk, ha⟩ := ValuationRecurrence.large_valuation_after hn N
  refine ⟨k, hk, ?_⟩
  have h := shadow_drop (orbit_odd hn k) (injective_shift hi k) ha
  rwa [orbit_succ] at h

/-- No constant additive correction can describe the exact coordinate
asymptotically on an injective orbit. This does not rule out that orbit. -/
theorem shadow_not_convergent {n : ℕ} (hn : Odd n) (hi : Function.Injective (orbit n))
    (L : ℝ) : ¬ Tendsto (fun k => shadow (orbit n k)) atTop (nhds L) := by
  intro h
  have hl := (tendsto_order.mp h).1 (L - 1 / 6) (by linarith)
  have hu := (tendsto_order.mp h).2 (L + 1 / 6) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hl.and hu)
  obtain ⟨k, hk, hd⟩ := arbitrarily_late_drop hn hi N
  have h0 := hN k hk
  have h1 := hN (k + 1) (by omega)
  linarith

end
end CollatzTargetDensity.ShadowOscillation
