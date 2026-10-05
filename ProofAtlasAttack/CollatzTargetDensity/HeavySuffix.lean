import CollatzTargetDensity.BoundaryLinearization

/-! An injective positive Syracuse orbit has a suffix with no coefficient
crossing. The analytic input is the proved summability of inverse terms.
No assertion that every integer has a coefficient crossing is made. -/
namespace CollatzTargetDensity.HeavySuffix
open Erdos1135 OrbitReciprocals InverseBoundary BoundaryLinearization Filter
open scoped BigOperators Topology
noncomputable section

theorem valuationTotal_shift (n m k : ℕ) :
    valuationTotal n (m + k) = valuationTotal n m + valuationTotal (orbit n m) k := by
  simp only [valuationTotal, Finset.sum_range_add, orbit_shift, Nat.add_comm]

theorem scale_shift (n m k : ℕ) :
    scale n (m + k) = scale n m * scale (orbit n m) k := by
  simp only [scale, valuationTotal_shift, pow_add]
  ring

theorem inverse_scale_tail {n : ℕ} (hn : 0 < n) (hi : Function.Injective (orbit n)) :
    ∃ N, ∀ k ≥ N, scale n k ≤ 1 := by
  have hs := (inverse_terms_summable hn hi).tendsto_atTop_zero
  have he := (tendsto_order.mp hs).2 (1 / 3 : ℝ) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  exact ⟨N, fun k hk => by have := hN k hk; linarith⟩

private theorem prefix_maximum (p : ℕ → ℝ) (N : ℕ) :
    ∃ m ≤ N, ∀ k ≤ N, p k ≤ p m := by
  induction N with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    intro k hk
    have : k = 0 := by omega
    simp [this]
  | succ N ih =>
    obtain ⟨m, hm, hmax⟩ := ih
    by_cases h : p (N + 1) ≤ p m
    · refine ⟨m, by omega, ?_⟩
      intro k hk
      by_cases hkN : k ≤ N
      · exact hmax k hkN
      · have : k = N + 1 := by omega
        simpa [this] using h
    · refine ⟨N + 1, le_rfl, ?_⟩
      intro k hk
      by_cases hkN : k ≤ N
      · exact (hmax k hkN).trans (le_of_not_ge h)
      · have : k = N + 1 := by omega
        simp [this]

/-- The actual analytic-to-arithmetic bridge: on some suffix of any
positive injective orbit, every inverse multiplicative coefficient is <=1. -/
theorem injective_has_heavy_suffix {n : ℕ} (hn : 0 < n)
    (hi : Function.Injective (orbit n)) :
    ∃ m, ∀ k, 2 ^ valuationTotal (orbit n m) k ≤ (3 : ℕ) ^ k := by
  obtain ⟨N, hN⟩ := inverse_scale_tail hn hi
  obtain ⟨m, hm, hmax⟩ := prefix_maximum (scale n) N
  have hglobal (j : ℕ) : scale n j ≤ scale n m := by
    by_cases hj : j ≤ N
    · exact hmax j hj
    · have hzero := hmax 0 (Nat.zero_le N)
      have he : scale n 0 = 1 := by simp [scale, valuationTotal]
      rw [he] at hzero
      exact (hN j (by omega)).trans hzero
  refine ⟨m, ?_⟩
  intro k
  have h := hglobal (m + k)
  rw [scale_shift] at h
  have hle : scale (orbit n m) k ≤ 1 := by
    apply (mul_le_mul_left (scale_pos n m)).mp
    simpa using h
  have hreal : (2 : ℝ) ^ valuationTotal (orbit n m) k ≤ (3 : ℝ) ^ k :=
    (div_le_one (by positivity)).mp hle
  exact_mod_cast hreal

/-- Universal coefficient crossing on odd positive starts would exclude
injective odd orbits. Universal crossing itself remains an assumption. -/
theorem not_injective_of_universal_crossing
    (hcross : ∀ a : ℕ, Odd a → ∃ k, (3 : ℕ) ^ k < 2 ^ valuationTotal a k)
    {n : ℕ} (hn : Odd n) : ¬ Function.Injective (orbit n) := by
  intro hi
  obtain ⟨m, hm⟩ := injective_has_heavy_suffix hn.pos hi
  have ho : Odd (orbit n m) := by
    cases m with
    | zero => simpa [orbit] using hn
    | succ m => rw [← orbit_succ]; exact Tao.syracuse_odd _
  obtain ⟨k, hk⟩ := hcross (orbit n m) ho
  exact (not_lt_of_ge (hm k)) hk

end
end CollatzTargetDensity.HeavySuffix
