import CollatzTargetDensity.SyracuseConcentration
import Erdos1135.ND.PositiveDensity.SyracuseBinaryAtomHeight

/-! Exact geometric-memory recurrence and collision energy for the actual law. -/
namespace CollatzTargetDensity.SyracuseEnergy
open Erdos1135 Erdos1135.ND.PositiveDensity SyracuseMinorant
open scoped BigOperators
noncomputable section

def lift (n : ℕ) (y : ZMod (3 ^ n)) : ZMod (3 ^ (n + 1)) := 3 * y.val + 1

def half (n : ℕ) (r : ZMod (3 ^ (n + 1))) : ZMod (3 ^ (n + 1)) := 2⁻¹ * r

theorem half_injective (n : ℕ) : Function.Injective (half n) := by
  intro r s h
  have hi := Tao.taoZModThreePow_inv_two_pow_mul (n + 1) 1
  simp only [pow_one] at hi
  have hh := congrArg (fun x : ZMod (3 ^ (n + 1)) => 2 * x) h
  simpa only [half, ← mul_assoc, mul_comm (2 : ZMod (3 ^ (n + 1))) 2⁻¹,
    hi, one_mul] using hh

theorem half_step (n : ℕ) (y : ZMod (3 ^ n)) (a : ℕ+) :
    Tao.syracStep n y (a + 1) = half n (Tao.syracStep n y a) := by
  have hi2 := Tao.taoZModThreePow_inv_two_pow_mul (n + 1) 1
  simp only [pow_one] at hi2
  have hia := Tao.taoZModThreePow_inv_two_pow_mul (n + 1) (a : ℕ)
  have hi : ((2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ) * 2)⁻¹ =
      2⁻¹ * ((2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ))⁻¹ := by
    apply ZMod.inv_eq_of_mul_eq_one
    calc
      _ = (2⁻¹ * (2 : ZMod (3 ^ (n + 1)))) *
          (((2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ))⁻¹ * 2 ^ (a : ℕ)) := by ring
      _ = 1 := by rw [hi2, hia, one_mul]
  simp only [Tao.syracStep, half, PNat.add_coe, PNat.val_ofNat, pow_succ, hi]
  ring

theorem step_one (n : ℕ) (y : ZMod (3 ^ n)) :
    Tao.syracStep n y 1 = half n (lift n y) := by
  simp [Tao.syracStep, half, lift]

theorem lift_injective (n : ℕ) : Function.Injective (lift n) := by
  intro y z h
  apply syracStep_fixedExponent_injective n 1
  simpa only [step_one] using congrArg (half n) h

theorem label_succ (n : ℕ) (r : ZMod (3 ^ (n + 1)))
    (y : ZMod (3 ^ n)) (a : ℕ+) :
    ndSyracuseFullReverseLabelMass n (half n r) y (a + 1) =
      ndSyracuseFullReverseLabelMass n r y a / 2 := by
  have he : Tao.syracStep n y (a + 1) = half n r ↔ Tao.syracStep n y a = r := by
    rw [half_step]
    exact (half_injective n).eq_iff
  unfold ndSyracuseFullReverseLabelMass
  rw [if_congr he rfl rfl]
  split_ifs
  · rw [Tao.geom2PNat_apply_toReal, Tao.geom2PNat_apply_toReal]
    simp only [PNat.add_coe, PNat.val_ofNat, pow_succ]
    ring
  · norm_num

theorem label_one (n : ℕ) (r : ZMod (3 ^ (n + 1))) (y : ZMod (3 ^ n)) :
    ndSyracuseFullReverseLabelMass n (half n r) y 1 =
      (if lift n y = r then (Tao.syracPMF n y).toReal else 0) / 2 := by
  have he : Tao.syracStep n y 1 = half n r ↔ lift n y = r := by
    rw [step_one]
    exact (half_injective n).eq_iff
  unfold ndSyracuseFullReverseLabelMass
  rw [if_congr he rfl rfl]
  split_ifs
  · simp [Tao.geom2PNat_apply_toReal]
    ring
  · norm_num

theorem tsum_pnat_first {f : ℕ+ → ℝ} (hf : Summable f) :
    ∑' a, f a = f 1 + ∑' a : ℕ+, f (a + 1) := by
  have hs := Equiv.pnatEquivNat.symm.summable_iff.mpr hf
  have hh := hs.tsum_eq_zero_add
  have he0 := Equiv.pnatEquivNat.symm.tsum_eq f
  have he1 := Equiv.pnatEquivNat.symm.tsum_eq (fun a : ℕ+ => f (a + 1))
  simpa only [Equiv.pnatEquivNat_symm_apply, ← he0, ← he1] using hh

def inputMass (n : ℕ) (r : ZMod (3 ^ (n + 1))) : ℝ :=
  ∑ y : ZMod (3 ^ n), if lift n y = r then (Tao.syracPMF n y).toReal else 0

/-- Geometric memorylessness, including its boundary injection. -/
theorem pmf_half_recurrence (n : ℕ) (r : ZMod (3 ^ (n + 1))) :
    (Tao.syracPMF (n + 1) (half n r)).toReal =
      ((Tao.syracPMF (n + 1) r).toReal + inputMass n r) / 2 := by
  have hlabel (y : ZMod (3 ^ n)) :
      (∑' a, ndSyracuseFullReverseLabelMass n (half n r) y a) =
        ((∑' a, ndSyracuseFullReverseLabelMass n r y a) +
          if lift n y = r then (Tao.syracPMF n y).toReal else 0) / 2 := by
    have hs : Summable (ndSyracuseFullReverseLabelMass n (half n r) y) := by
      simpa using summable_ndSyracuseFullReverseLabelMass n (half n r).val y
    rw [tsum_pnat_first hs, label_one]
    simp_rw [label_succ]
    rw [tsum_div_const]
    ring
  rw [← sum_ndSyracuseFullReverseLabelMass_eq_syracPMF]
  simp_rw [hlabel]
  rw [← Finset.sum_div, Finset.sum_add_distrib, sum_ndSyracuseFullReverseLabelMass_eq_syracPMF]
  rfl

theorem inputMass_lift (n : ℕ) (y : ZMod (3 ^ n)) :
    inputMass n (lift n y) = (Tao.syracPMF n y).toReal := by
  classical
  simp [inputMass, (lift_injective n).eq_iff]

theorem sum_mul_inputMass (n : ℕ) (f : ZMod (3 ^ (n + 1)) → ℝ) :
    (∑ r, f r * inputMass n r) =
      ∑ y : ZMod (3 ^ n), f (lift n y) * (Tao.syracPMF n y).toReal := by
  classical
  simp only [inputMass, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

theorem sum_inputMass_sq (n : ℕ) :
    (∑ r : ZMod (3 ^ (n + 1)), (inputMass n r) ^ 2) =
      ∑ y : ZMod (3 ^ n), (Tao.syracPMF n y).toReal ^ 2 := by
  simp_rw [pow_two]
  rw [sum_mul_inputMass]
  simp_rw [inputMass_lift]

def collisionEnergy (n : ℕ) : ℝ :=
  (3 : ℝ) ^ n * ∑ y : ZMod (3 ^ n), (Tao.syracPMF n y).toReal ^ 2

theorem collisionEnergy_eq_haar_secondMoment (n : ℕ) :
    collisionEnergy n =
      (∑ r : ZMod (3 ^ n), (ndSyracuseUniformDensity n r) ^ 2) / (3 : ℝ) ^ n := by
  unfold collisionEnergy ndSyracuseUniformDensity Tao.syracPMFMassVector
  push_cast
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]
  field_simp

/-- Exact energy increment; all terms retain the actual Syracuse PMF. -/
theorem collisionEnergy_recurrence (n : ℕ) :
    collisionEnergy (n + 1) = collisionEnergy n +
      2 * (3 : ℝ) ^ n * ∑ y : ZMod (3 ^ n),
        (Tao.syracPMF (n + 1) (lift n y)).toReal * (Tao.syracPMF n y).toReal := by
  classical
  have hp : (∑ r : ZMod (3 ^ (n + 1)),
      (Tao.syracPMF (n + 1) (half n r)).toReal ^ 2) =
      ∑ r : ZMod (3 ^ (n + 1)), (Tao.syracPMF (n + 1) r).toReal ^ 2 := by
    let e := Equiv.ofBijective (half n)
      ⟨half_injective n, Finite.surjective_of_injective (half_injective n)⟩
    exact Equiv.sum_comp e (fun r => (Tao.syracPMF (n + 1) r).toReal ^ 2)
  have hlocal (r : ZMod (3 ^ (n + 1))) :
      4 * (Tao.syracPMF (n + 1) (half n r)).toReal ^ 2 =
        (Tao.syracPMF (n + 1) r).toReal ^ 2 + (inputMass n r) ^ 2 +
          2 * ((Tao.syracPMF (n + 1) r).toReal * inputMass n r) := by
    rw [pmf_half_recurrence]
    ring
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun r _ => hlocal r)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hp,
    sum_inputMass_sq, sum_mul_inputMass] at hsum
  unfold collisionEnergy
  rw [pow_succ]
  have hm := congrArg (fun x : ℝ => (3 : ℝ) ^ n * x) hsum
  nlinarith [hm]

theorem lift_isUnit (n : ℕ) (y : ZMod (3 ^ n)) : IsUnit (lift n y) := by
  have hc : Nat.Coprime (3 * y.val + 1) 3 := by
    simp [Nat.coprime_mul_left_add_left]
  have hu := (ZMod.isUnit_iff_coprime (3 * y.val + 1) (3 ^ (n + 1))).mpr
    (hc.pow_right (n + 1))
  simpa [lift] using hu

theorem pmf_sum (n : ℕ) : (∑ y : ZMod (3 ^ n), (Tao.syracPMF n y).toReal) = 1 := by
  have hh : (∑' y : ZMod (3 ^ n), (Tao.syracPMF n y).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq]
    · rw [PMF.tsum_coe, ENNReal.toReal_one]
    · intro y
      exact (Tao.syracPMF n).apply_ne_top y
  simpa only [tsum_fintype] using hh

/-- A positive atom floor creates a strictly positive increment at every depth. -/
theorem collisionEnergy_gain_of_floor (c : ℝ)
    (hf : ∀ n : ℕ, 1 ≤ n → ∀ r : ZMod (3 ^ n), IsUnit r →
      c / (3 : ℝ) ^ n ≤ (Tao.syracPMF n r).toReal) (n : ℕ) :
    collisionEnergy n + 2 * c / 3 ≤ collisionEnergy (n + 1) := by
  have hsum : c / (3 : ℝ) ^ (n + 1) ≤
      ∑ y : ZMod (3 ^ n),
        (Tao.syracPMF (n + 1) (lift n y)).toReal * (Tao.syracPMF n y).toReal := by
    calc
      c / (3 : ℝ) ^ (n + 1) =
          ∑ y : ZMod (3 ^ n), c / (3 : ℝ) ^ (n + 1) *
            (Tao.syracPMF n y).toReal := by rw [← Finset.mul_sum, pmf_sum, mul_one]
      _ ≤ _ := Finset.sum_le_sum (fun y _ =>
        mul_le_mul_of_nonneg_right (hf (n + 1) (by omega) (lift n y) (lift_isUnit n y))
          ENNReal.toReal_nonneg)
  have hh := mul_le_mul_of_nonneg_left hsum
    (show (0 : ℝ) ≤ 2 * 3 ^ n by positivity)
  have he : 2 * (3 : ℝ) ^ n * (c / (3 : ℝ) ^ (n + 1)) = 2 * c / 3 := by
    rw [pow_succ]
    field_simp
  rw [he] at hh
  rw [collisionEnergy_recurrence]
  linarith

theorem collisionEnergy_zero : collisionEnergy 0 = 1 := by
  have hzero (y : ZMod (3 ^ 0)) : y = 0 := by
    exact Subsingleton.elim (α := ZMod 1) y 0
  have hmass (y : ZMod (3 ^ 0)) : Tao.syracPMF 0 y = 1 := by
    rw [hzero y, Tao.syracPMF_zero_apply_zero]
  simp [collisionEnergy, hmass]

/-- Unconditional consequence of the previously checked uniform atom floor. -/
theorem exists_linear_collisionEnergy_lower :
    ∃ d : ℝ, 0 < d ∧ ∀ n : ℕ, 1 + d * n ≤ collisionEnergy n := by
  obtain ⟨c, hc, hf⟩ := syracuse_uniform_atom_lower_bound
  refine ⟨2 * c / 3, by positivity, ?_⟩
  intro n
  induction n with
  | zero => simp [collisionEnergy_zero]
  | succ n ih =>
    have hh := collisionEnergy_gain_of_floor c hf n
    push_cast
    linarith

theorem no_uniform_collisionEnergy_upper :
    ¬ ∃ C : ℝ, ∀ n : ℕ, collisionEnergy n ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨d, hd, hlower⟩ := exists_linear_collisionEnergy_lower
  obtain ⟨n, hn⟩ := exists_nat_gt ((C - 1) / d)
  have hh := (div_lt_iff₀ hd).mp hn
  have := (hlower n).trans (hC n)
  nlinarith

end
end CollatzTargetDensity.SyracuseEnergy
