import CollatzTargetDensity.SyracusePositiveCylinder

/-! Fixed-cylinder projection of the one-sided comparison. -/
namespace CollatzTargetDensity.SyracuseMinorant
open Erdos1135 Erdos1135.ND.PositiveDensity Filter
open scoped BigOperators Topology
noncomputable section

theorem projection_fiber_const {h q : ℕ} (hhq : h ≤ q)
    (x : ZMod (3 ^ h)) (a : ℝ) :
    (∑ y : ZMod (3 ^ q), if Tao.taoZModThreeProjection hhq y = x then a else 0) =
      (3 : ℝ) ^ (q - h) * a := by
  classical
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype _ (by simp : ∀ y : ZMod (3 ^ q),
    y ∈ Finset.univ.filter (fun y => Tao.taoZModThreeProjection hhq y = x) ↔
      Tao.taoZModThreeProjection hhq y = x)]
  have hc : Fintype.card {y : ZMod (3 ^ q) // Tao.taoZModThreeProjection hhq y = x} =
      3 ^ (q - h) := Tao.taoZModThreeProjection_fiber_card hhq x
  rw [Finset.sum_const, Finset.card_univ, hc]
  simp

theorem projection_fiber_density {h q : ℕ} (hhq : h ≤ q)
    (x : ZMod (3 ^ h)) :
    (∑ y : ZMod (3 ^ q), if Tao.taoZModThreeProjection hhq y = x then
      ndSyracuseUnitReferenceDensity q y else 0) =
      (3 : ℝ) ^ (q - h) * ndSyracuseUnitReferenceDensity h x := by
  classical
  have hmass : (∑ y : ZMod (3 ^ q), if Tao.taoZModThreeProjection hhq y = x then
      (Tao.syracPMF q y).toReal else 0) = (Tao.syracPMF h x).toReal := by
    have he := congrArg (fun p => (p x).toReal)
      (Tao.syracPMF_map_taoZModThreeProjection_eq_of_le hhq)
    dsimp only at he
    rw [Tao.pmf_map_apply_toReal_tsum, tsum_fintype] at he
    simpa only [eq_comm] using he
  unfold ndSyracuseUnitReferenceDensity ndSyracuseUniformDensity Tao.syracPMFMassVector
  simp_rw [← mul_assoc]
  rw [show (∑ y : ZMod (3 ^ q), if Tao.taoZModThreeProjection hhq y = x then
      (2 / 3 : ℝ) * (3 ^ q : ℕ) * (Tao.syracPMF q y).toReal else 0) =
      (2 / 3 : ℝ) * (3 ^ q : ℕ) * ∑ y : ZMod (3 ^ q),
        if Tao.taoZModThreeProjection hhq y = x then (Tao.syracPMF q y).toReal else 0 by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; split_ifs <;> simp]
  rw [hmass]
  push_cast
  have hp : (3 : ℝ) ^ q = 3 ^ (q - h) * 3 ^ h := by
    rw [← pow_add, Nat.sub_add_cancel hhq]
  rw [hp]
  ring

/-- The test conductor h is fixed; the factor is 3^h, not 3^q. -/
theorem fiber_lower_of_positive_error {h q : ℕ} (hhq : h ≤ q)
    (x : ZMod (3 ^ h)) (g : ZMod (3 ^ q) → ℝ) (a : ℝ)
    (hg : ∀ y, Tao.taoZModThreeProjection hhq y = x → a ≤ g y) :
    a ≤ ndSyracuseUnitReferenceDensity h x + (3 : ℝ) ^ h *
      ndTernaryUniformMean q (fun y => max (g y - ndSyracuseUnitReferenceDensity q y) 0) := by
  classical
  have hsum : (∑ y : ZMod (3 ^ q), if Tao.taoZModThreeProjection hhq y = x then a else 0) ≤
      (∑ y : ZMod (3 ^ q), if Tao.taoZModThreeProjection hhq y = x then
        ndSyracuseUnitReferenceDensity q y else 0) +
      ∑ y : ZMod (3 ^ q), max (g y - ndSyracuseUnitReferenceDensity q y) 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro y _
    by_cases hy : Tao.taoZModThreeProjection hhq y = x
    · simp only [if_pos hy]
      have := hg y hy
      have := le_max_left (g y - ndSyracuseUnitReferenceDensity q y) 0
      linarith
    · simp only [if_neg hy, zero_add]
      exact le_max_right _ _
  rw [projection_fiber_const, projection_fiber_density] at hsum
  have hp : (3 : ℝ) ^ q = 3 ^ (q - h) * 3 ^ h := by
    rw [← pow_add, Nat.sub_add_cancel hhq]
  unfold ndTernaryUniformMean ndTernaryUniformScale
  push_cast
  apply le_of_mul_le_mul_left _ (show (0 : ℝ) < 3 ^ (q - h) by positivity)
  calc
    _ ≤ _ := hsum
    _ = _ := by rw [hp]; field_simp

theorem coreMark_positive_error_rate {b : ℕ} (hb : 200 ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      ndTernaryUniformMean (ambientConductor b n) (fun y =>
        max (coreMark b n y - ndSyracuseUnitReferenceDensity (ambientConductor b n) y) 0) ≤
        C / (n : ℝ) := by
  obtain ⟨C, hC, hr⟩ := backward_mark_positive_error_polynomial 2 (by norm_num)
  refine ⟨4 * C, by positivity, ?_⟩
  intro n hn
  have hk := terminalConductor_pos hb n
  have hnk := generation_le_twice_terminal hb n
  have hbase := hr b (fun n => n / 100) ndRootCoreWidth
    (terminalConductor b n) n hk
  refine hbase.trans ?_
  have hkR : 0 < (terminalConductor b n : ℝ) := by exact_mod_cast hk
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnkR : (n : ℝ) ≤ 2 * (terminalConductor b n : ℝ) := by exact_mod_cast hnk
  apply (le_div_iff₀ hnR).2
  rw [← mul_div_assoc, div_mul_eq_mul_div]
  apply (div_le_iff₀ (sq_pos_of_pos hkR)).2
  have hs : (n : ℝ) ^ 2 ≤ 4 * (terminalConductor b n : ℝ) ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_left hs hC
  nlinarith

/-- The actual Syracuse densities are bounded below on every finer subcell
of one fixed positive unit cylinder. No moving-conductor limit is used. -/
theorem exists_positive_syracuse_cylinder :
    ∃ (q : ℕ) (y : ZMod (3 ^ q)) (a : ℝ),
      1 ≤ q ∧ IsUnit (y.val : ZMod (3 ^ 1)) ∧ 0 < a ∧
      ∀ h, ∀ hqh : q ≤ h, ∀ x : ZMod (3 ^ h),
        Tao.taoZModThreeProjection hqh x = y →
        a ≤ ndSyracuseUnitReferenceDensity h x := by
  let b : ℕ := 32 ^ 5
  have hb : 32 ^ 5 ≤ b := le_rfl
  obtain ⟨q, N, y, a, hq, hy, ha, hmark⟩ := exists_fixed_positive_core_cylinder_finite hb
  obtain ⟨C, hC, herr⟩ := coreMark_positive_error_rate (b := b) (by norm_num [b])
  refine ⟨q, y, a, hq, hy, ha, ?_⟩
  intro h hqh x hx
  by_contra hnot
  have hdelta : 0 < a - ndSyracuseUnitReferenceDensity h x := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (max ((N + 2 * h + 1 : ℕ) : ℝ)
    (C * (3 : ℝ) ^ h / (a - ndSyracuseUnitReferenceDensity h x)))
  have hlarge : N + 2 * h + 1 < n := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hn)
  have hratio : C * (3 : ℝ) ^ h / (a - ndSyracuseUnitReferenceDensity h x) < n :=
    lt_of_le_of_lt (le_max_right _ _) hn
  have hn0 : 0 < n := by omega
  have hhn : h ≤ ambientConductor b n := by
    have := generation_le_twice_terminal (b := b) (by norm_num [b]) n
    have := terminal_le_ambient b n
    omega
  have hpoint := fiber_lower_of_positive_error hhn x (coreMark b n) a (by
    intro z hz
    apply hmark n (by omega) (hqh.trans hhn) z
    rw [← Tao.taoZModThreeProjection_comp_apply hqh hhn, hz, hx])
  have herror := herr n hn0
  have hupper : a ≤ ndSyracuseUnitReferenceDensity h x + (3 : ℝ) ^ h * (C / (n : ℝ)) :=
    hpoint.trans (by gcongr)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hstrict : (3 : ℝ) ^ h * (C / (n : ℝ)) < a - ndSyracuseUnitReferenceDensity h x := by
    have hh := (div_lt_iff₀ hdelta).mp hratio
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hnR).2
    nlinarith
  linarith

end
end CollatzTargetDensity.SyracuseMinorant
