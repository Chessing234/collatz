import CollatzTargetDensity.SyracuseCylinderProjection
import CollatzTargetDensity.TernarySpread
import Erdos1135.ND.PositiveDensity.CommonZFullReverseKernel

/-! Bounded inverse coverage and propagation of a positive Syracuse cylinder. -/
namespace CollatzTargetDensity.SyracuseMinorant
open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators
noncomputable section

theorem syracStep_natCast_of_equation (h c : ℕ) (v : ℕ+)
    (r : ZMod (3 ^ (h + 1))) (he : 3 * c + 1 = 2 ^ (v : ℕ) * r.val) :
    Tao.syracStep h (c : ZMod (3 ^ h)) v = r := by
  have hm : 3 * (c % 3 ^ h) + 1 ≡ 3 * c + 1 [MOD 3 ^ (h + 1)] := by
    simpa only [pow_succ, Nat.mul_comm] using
      ((Nat.mod_modEq c (3 ^ h)).mul_left' 3).add_right 1
  rw [he] at hm
  have hc := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm
  have hinner : (3 : ZMod (3 ^ (h + 1))) * (c % 3 ^ h : ℕ) + 1 =
      (2 : ZMod (3 ^ (h + 1))) ^ (v : ℕ) * r := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one, ZMod.natCast_zmod_val] using hc
  unfold Tao.syracStep
  rw [ZMod.val_natCast, hinner, ← mul_assoc,
    Tao.taoZModThreePow_inv_two_pow_mul, one_mul]

/-- Every unit target has a one-step inverse in a prescribed q-cylinder,
with valuation bounded in terms of q alone, independently of target depth. -/
theorem bounded_inverse_into_cylinder (q h : ℕ) (hqh : q ≤ h)
    (y : ZMod (3 ^ q)) (r : ZMod (3 ^ (h + 1))) (hr : r.val % 3 ≠ 0) :
    ∃ (v : ℕ+) (z : ZMod (3 ^ h)),
      (v : ℕ) ≤ 2 * 3 ^ q + 2 ∧
      Tao.taoZModThreeProjection hqh z = y ∧ Tao.syracStep h z v = r := by
  have hbase : ∃ c e : ℕ, 1 ≤ e ∧ e ≤ 2 ∧ 3 * c + 1 = 2 ^ e * r.val := by
    by_cases hr1 : r.val % 3 = 1
    · refine ⟨(4 * r.val - 1) / 3, 2, by omega, by omega, ?_⟩
      norm_num
      omega
    · refine ⟨(2 * r.val - 1) / 3, 1, by omega, by omega, ?_⟩
      norm_num
      omega
  obtain ⟨c, e, he0, he2, he⟩ := hbase
  obtain ⟨t, ht, hres⟩ := sibling_residue q c ⟨y.val, y.val_lt⟩
  let v : ℕ+ := ⟨2 * t + e, by omega⟩
  let z : ZMod (3 ^ h) := sibling t c
  refine ⟨v, z, by dsimp [v]; omega, ?_, ?_⟩
  · change Tao.taoZModThreeProjection hqh (sibling t c : ZMod (3 ^ h)) = y
    rw [Tao.taoZModThreeProjection_natCast]
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast] using hres
  · apply syracStep_natCast_of_equation h (sibling t c) v r
    have hsource := three_mul_ndA5PreviousPhysicalCollapseSource_add_one t
    have hp : (2 : ℕ) ^ (2 * t) = 4 ^ t := by rw [pow_mul]; norm_num
    change 3 * sibling t c + 1 = 2 ^ (2 * t + e) * r.val
    rw [pow_add, hp, mul_assoc, ← he]
    unfold sibling
    nlinarith

theorem syracPMF_single_reverse_le (h : ℕ) (r : ZMod (3 ^ (h + 1)))
    (z : ZMod (3 ^ h)) (v : ℕ+) (he : Tao.syracStep h z v = r) :
    (Tao.syracPMF h z).toReal * (1 / 2 : ℝ) ^ (v : ℕ) ≤
      (Tao.syracPMF (h + 1) r).toReal := by
  classical
  have hs : Summable (fun a => ndSyracuseFullReverseLabelMass h r z a) := by
    simpa using summable_ndSyracuseFullReverseLabelMass h r.val z
  have hsingle := hs.le_tsum v (fun a _ => ndSyracuseFullReverseLabelMass_nonneg h r z a)
  have houter := Finset.single_le_sum
    (f := fun y => ∑' a : ℕ+, ndSyracuseFullReverseLabelMass h r y a)
    (fun y _ => tsum_nonneg (fun a => ndSyracuseFullReverseLabelMass_nonneg h r y a))
    (Finset.mem_univ z)
  rw [sum_ndSyracuseFullReverseLabelMass_eq_syracPMF] at houter
  have hh := hsingle.trans houter
  simpa only [ndSyracuseFullReverseLabelMass, if_pos he, Tao.geom2PNat_apply_toReal] using hh

theorem referenceDensity_single_reverse_le (h : ℕ) (r : ZMod (3 ^ (h + 1)))
    (z : ZMod (3 ^ h)) (v : ℕ+) (he : Tao.syracStep h z v = r) :
    3 * (1 / 2 : ℝ) ^ (v : ℕ) * ndSyracuseUnitReferenceDensity h z ≤
      ndSyracuseUnitReferenceDensity (h + 1) r := by
  have hh := mul_le_mul_of_nonneg_left (syracPMF_single_reverse_le h r z v he)
    (show (0 : ℝ) ≤ (2 / 3) * 3 ^ (h + 1) by positivity)
  unfold ndSyracuseUnitReferenceDensity ndSyracuseUniformDensity Tao.syracPMFMassVector
  push_cast
  simpa only [pow_succ] using (by convert hh using 1 <;> ring)

theorem unit_residue_of_projection {h H : ℕ} (hh : 1 ≤ h) (hle : h ≤ H)
    (z : ZMod (3 ^ H)) (x : ZMod (3 ^ h))
    (he : Tao.taoZModThreeProjection hle z = x) (hx : x.val % 3 ≠ 0) :
    z.val % 3 ≠ 0 := by
  have hv := congrArg ZMod.val he
  rw [Tao.taoZModThreeProjection_eq_natCast_val, ZMod.val_natCast] at hv
  rw [← hv, Nat.mod_mod_of_dvd _ (dvd_pow_self 3 (by omega : h ≠ 0))] at hx
  exact hx

/-- A depth-independent lower bound for the actual normalized Syracuse
density on every unit residue. -/
theorem exists_uniform_positive_syracuse_density :
    ∃ c : ℝ, 0 < c ∧ ∀ h : ℕ, 1 ≤ h → ∀ r : ZMod (3 ^ h),
      r.val % 3 ≠ 0 → c ≤ ndSyracuseUnitReferenceDensity h r := by
  obtain ⟨q, y, a, hq, _, ha, hfloor⟩ := exists_positive_syracuse_cylinder
  let V : ℕ := 2 * 3 ^ q + 2
  let c : ℝ := 3 * (1 / 2 : ℝ) ^ V * a
  have hc : 0 < c := by dsimp [c]; positivity
  have hlarge : ∀ h : ℕ, q + 1 ≤ h → ∀ r : ZMod (3 ^ h), r.val % 3 ≠ 0 →
      c ≤ ndSyracuseUnitReferenceDensity h r := by
    intro h hh r hr
    cases h with
    | zero => omega
    | succ h =>
      have hqh : q ≤ h := by omega
      obtain ⟨v, z, hv, hz, he⟩ := bounded_inverse_into_cylinder q h hqh y r hr
      have hzfloor := hfloor h hqh z hz
      have hp : (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ (v : ℕ) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hv
      have hstep := referenceDensity_single_reverse_le h r z v he
      apply le_trans _ hstep
      dsimp [c]
      calc
        3 * (1 / 2 : ℝ) ^ V * a ≤ 3 * (1 / 2 : ℝ) ^ (v : ℕ) * a := by gcongr
        _ ≤ 3 * (1 / 2 : ℝ) ^ (v : ℕ) * ndSyracuseUnitReferenceDensity h z := by gcongr
  refine ⟨c, hc, ?_⟩
  intro h hh r hr
  by_cases hbig : q + 1 ≤ h
  · exact hlarge h hbig r hr
  · have hle : h ≤ q + 1 := by omega
    classical
    have hsum : (∑ z : ZMod (3 ^ (q + 1)),
        if Tao.taoZModThreeProjection hle z = r then c else 0) ≤
      ∑ z : ZMod (3 ^ (q + 1)), if Tao.taoZModThreeProjection hle z = r then
        ndSyracuseUnitReferenceDensity (q + 1) z else 0 := by
      apply Finset.sum_le_sum
      intro z _
      split_ifs with hz
      · exact hlarge (q + 1) le_rfl z (unit_residue_of_projection hh hle z r hz hr)
      · rfl
    rw [projection_fiber_const, projection_fiber_density] at hsum
    exact le_of_mul_le_mul_left hsum (by positivity : (0 : ℝ) < 3 ^ (q + 1 - h))

/-- Literal probability statement: the constant is independent of both
conductor and unit residue. The law is the imported Geom(2) Syracuse PMF. -/
theorem syracuse_uniform_atom_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ r : ZMod (3 ^ n),
      IsUnit r → c / (3 : ℝ) ^ n ≤ (Tao.syracPMF n r).toReal := by
  obtain ⟨c, hc, hfloor⟩ := exists_uniform_positive_syracuse_density
  refine ⟨(3 / 2) * c, by positivity, ?_⟩
  intro n hn r hr
  have hl : IsUnit (r.val : ZMod (3 ^ 1)) := by
    have hh := hr.map (Tao.taoZModThreeProjection hn)
    rwa [Tao.taoZModThreeProjection_eq_natCast_val] at hh
  have hres : r.val % 3 ≠ 0 := by
    intro hz
    have hzero : (r.val : ZMod (3 ^ 1)) = 0 := by
      apply ZMod.val_injective
      simpa only [ZMod.val_natCast, pow_one, ZMod.val_zero] using hz
    rw [hzero] at hl
    change IsUnit (0 : ZMod 3) at hl
    exact not_isUnit_zero hl
  have hh := hfloor n hn r hres
  unfold ndSyracuseUnitReferenceDensity ndSyracuseUniformDensity Tao.syracPMFMassVector at hh
  push_cast at hh
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 ^ n)).2
  nlinarith

end
end CollatzTargetDensity.SyracuseMinorant
