import CollatzTargetDensity.EnergyTargets

/-!
An unconditional improvement of the elementary exponential energy bound.
The two unit classes modulo three have an exact factor-two relation.
This is an estimate for the actual Syracuse probability law, not a proof
of deterministic Collatz convergence or of linear energy growth.
-/
namespace CollatzTargetDensity.SyracuseEnergy
open Erdos1135
open scoped BigOperators
noncomputable section

theorem lift_ne_two_lift (n : ℕ) (x y : ZMod (3 ^ n)) :
    lift n x ≠ 2 * lift n y := by
  intro h
  let red : ZMod (3 ^ (n + 1)) →+* ZMod 3 :=
    ZMod.castHom (dvd_pow_self 3 (by omega : n + 1 ≠ 0)) (ZMod 3)
  have hr := congrArg red h
  have h3 : red (3 : ZMod (3 ^ (n + 1))) = 0 := by
    change (ZMod.cast ((3 : ℕ) : ZMod (3 ^ (n + 1))) : ZMod 3) = 0
    rw [ZMod.cast_natCast (dvd_pow_self 3 (by omega : n + 1 ≠ 0))]
    decide
  have h2 : red (2 : ZMod (3 ^ (n + 1))) = 2 := by
    change (ZMod.cast ((2 : ℕ) : ZMod (3 ^ (n + 1))) : ZMod 3) = (2 : ℕ)
    exact ZMod.cast_natCast (dvd_pow_self 3 (by omega : n + 1 ≠ 0)) 2
  simp only [lift, map_add, map_mul, h3, h2, map_one, zero_mul, zero_add, mul_one] at hr
  exact (by decide : (1 : ZMod 3) ≠ 2) hr

theorem inputMass_two_lift (n : ℕ) (y : ZMod (3 ^ n)) :
    inputMass n (2 * lift n y) = 0 := by
  classical
  simp [inputMass, lift_ne_two_lift]

theorem pmf_two_lift (n : ℕ) (y : ZMod (3 ^ n)) :
    (Tao.syracPMF (n + 1) (2 * lift n y)).toReal =
      2 * (Tao.syracPMF (n + 1) (lift n y)).toReal := by
  have hi := Tao.taoZModThreePow_inv_two_pow_mul (n + 1) 1
  simp only [pow_one] at hi
  have h := pmf_half_recurrence n (2 * lift n y)
  have he : half n (2 * lift n y) = lift n y := by
    simp only [half, ← mul_assoc, hi, one_mul]
  rw [he, inputMass_two_lift] at h
  linarith

def unitClassEmbedding (n : ℕ) : ZMod (3 ^ n) ⊕ ZMod (3 ^ n) → ZMod (3 ^ (n + 1))
  | Sum.inl y => lift n y
  | Sum.inr y => 2 * lift n y

theorem unitClassEmbedding_injective (n : ℕ) : Function.Injective (unitClassEmbedding n) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl ((lift_injective n) h)
    | inr b => exact False.elim (lift_ne_two_lift n a b h)
  | inr a =>
    cases b with
    | inl b => exact False.elim (lift_ne_two_lift n b a h.symm)
    | inr b =>
      have hi := Tao.taoZModThreePow_inv_two_pow_mul (n + 1) 1
      simp only [pow_one] at hi
      have hh := congrArg (fun x : ZMod (3 ^ (n + 1)) => 2⁻¹ * x) h
      simp only [unitClassEmbedding, ← mul_assoc, hi, one_mul] at hh
      exact congrArg Sum.inr ((lift_injective n) hh)

/-- At least five times the squared mass on class 1 is present in the
full law: class 2 is an injectively paired copy with twice the mass. -/
theorem five_mul_lift_square_sum_le (n : ℕ) :
    5 * (∑ y : ZMod (3 ^ n), (Tao.syracPMF (n + 1) (lift n y)).toReal ^ 2) ≤
      ∑ r : ZMod (3 ^ (n + 1)), (Tao.syracPMF (n + 1) r).toReal ^ 2 := by
  classical
  let f := fun r : ZMod (3 ^ (n + 1)) => (Tao.syracPMF (n + 1) r).toReal ^ 2
  have h := Finset.sum_le_univ_sum_of_nonneg (f := f)
    (s := Finset.univ.image (unitClassEmbedding n)) (fun _ => sq_nonneg _)
  rw [Finset.sum_image (fun a _ b _ h => unitClassEmbedding_injective n h)] at h
  rw [Fintype.sum_sum_type] at h
  simp only [unitClassEmbedding, f, pmf_two_lift, mul_pow] at h
  rw [← Finset.mul_sum] at h
  norm_num at h
  linarith

theorem collisionEnergy_step_le_five_thirds (n : ℕ) :
    collisionEnergy (n + 1) ≤ (5 / 3 : ℝ) * collisionEnergy n := by
  let Q := ∑ y : ZMod (3 ^ n), (Tao.syracPMF n y).toReal ^ 2
  let R := ∑ r : ZMod (3 ^ (n + 1)), (Tao.syracPMF (n + 1) r).toReal ^ 2
  let L := ∑ y : ZMod (3 ^ n), (Tao.syracPMF (n + 1) (lift n y)).toReal ^ 2
  let C := ∑ y : ZMod (3 ^ n),
    (Tao.syracPMF (n + 1) (lift n y)).toReal * (Tao.syracPMF n y).toReal
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  have hL : 5 * L ≤ R := five_mul_lift_square_sum_le n
  have hCS : C ^ 2 ≤ L * Q := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hrec := collisionEnergy_recurrence n
  change (3 : ℝ) ^ (n + 1) * R = 3 ^ n * Q + 2 * 3 ^ n * C at hrec
  rw [pow_succ] at hrec
  have hpow : (0 : ℝ) < 3 ^ n := by positivity
  have hraw : 3 * R = Q + 2 * C := by
    apply (mul_left_cancel₀ hpow.ne')
    nlinarith [hrec]
  have hbound : 3 * C ≤ Q := by
    by_contra hnot
    have hp : 0 < (3 * C - Q) * (5 * C + Q) := by
      apply mul_pos <;> linarith
    have hprod := mul_le_mul_of_nonneg_right hL hQ
    nlinarith [hCS, hprod, hraw]
  have hR : R ≤ (5 / 9 : ℝ) * Q := by linarith
  change (3 : ℝ) ^ (n + 1) * R ≤ (5 / 3 : ℝ) * (3 ^ n * Q)
  rw [pow_succ]
  nlinarith [mul_le_mul_of_nonneg_left hR hpow.le]

theorem collisionEnergy_le_five_thirds_pow (n : ℕ) :
    collisionEnergy n ≤ (5 / 3 : ℝ) ^ n := by
  induction n with
  | zero => simp [collisionEnergy_zero]
  | succ n ih =>
    calc
      collisionEnergy (n + 1) ≤ (5 / 3 : ℝ) * collisionEnergy n := collisionEnergy_step_le_five_thirds n
      _ ≤ (5 / 3 : ℝ) * (5 / 3 : ℝ) ^ n := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (5 / 3 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

end
end CollatzTargetDensity.SyracuseEnergy

namespace CollatzTargetDensity
open Erdos1135 SyracuseEnergy
noncomputable section

/-- The improved energy estimate inserted into the existing ordinary
predecessor count. This still has exponential loss, not cubic density. -/
theorem five_thirds_target_density (A : ℕ) (hA : 1 ≤ A) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ d : ℝ, 0 < d ∧
      ∀ a : ℕ, 0 < a → a % 3 ≠ 0 →
      ∀ t : ℕ, 1 ≤ t → a ≤ t ^ A →
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        d / ((a : ℝ) ^ 2 * (5 / 3 : ℝ) ^ (K * t)) * (X : ℝ) ≤ countBelow a X := by
  obtain ⟨K, hK, d, hd, hcount⟩ := energy_target_density A hA
  refine ⟨K, hK, d, hd, ?_⟩
  intro a ha hthree t ht hat
  obtain ⟨X₀, hX₀⟩ := hcount a ha hthree t ht hat
  refine ⟨X₀, ?_⟩
  intro X hX
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hE := collisionEnergy_pos (K * t)
  have hcoeff : d / ((a : ℝ) ^ 2 * (5 / 3 : ℝ) ^ (K * t)) ≤
      d / ((a : ℝ) ^ 2 * collisionEnergy (K * t)) := by
    exact div_le_div_of_nonneg_left hd.le (by positivity)
      (mul_le_mul_of_nonneg_left (collisionEnergy_le_five_thirds_pow (K * t)) (sq_nonneg _))
  exact (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg X)).trans (hX₀ X hX)

end
end CollatzTargetDensity
