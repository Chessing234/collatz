import CollatzTargetDensity.SyracuseEnergyUpper
import Mathlib.Analysis.InnerProductSpace.PiL2
import Erdos1135.ND.PositiveDensity.CommonZBoundaryExponentTwoDescent

/-!
Residue-class refinement of the unconditional Syracuse collision-energy bound.
All estimates below concern the actual law; they do not assert convergence.
-/
namespace CollatzTargetDensity.SyracuseEnergy
open Erdos1135
open scoped BigOperators
noncomputable section

namespace FiniteL2
variable {X : Type*} [Fintype X]

def size (f : X → ℝ) : ℝ := ‖(WithLp.toLp 2 f : EuclideanSpace ℝ X)‖

theorem nonneg (f : X → ℝ) : 0 ≤ size f := norm_nonneg _

theorem sq_eq (f : X → ℝ) : size f ^ 2 = ∑ x, f x ^ 2 := by
  exact EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 f)

theorem add_le (f g : X → ℝ) : size (fun x => f x + g x) ≤ size f + size g := by
  exact norm_add_le (WithLp.toLp 2 f) (WithLp.toLp 2 g)

theorem scale (a : ℝ) (ha : 0 ≤ a) (f : X → ℝ) :
    size (fun x => a * f x) = a * size f := by
  change ‖a • (WithLp.toLp 2 f : EuclideanSpace ℝ X)‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  rfl

theorem comp (e : X ≃ X) (f : X → ℝ) : size (fun x => f (e x)) = size f := by
  apply (sq_eq_sq₀ (nonneg _) (nonneg _)).mp
  simp only [sq_eq]
  exact Equiv.sum_comp e (fun x => f x ^ 2)

theorem dot_le (f g : X → ℝ) : ∑ x, f x * g x ≤ size f * size g := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  rw [← sq_eq, ← sq_eq] at h
  have hf := nonneg f
  have hg := nonneg g
  nlinarith [mul_nonneg hf hg]

def part (c : X → ZMod 3) (i : ZMod 3) (f : X → ℝ) (x : X) : ℝ :=
  if c x = i then f x else 0

omit [Fintype X] in
theorem part_add (c : X → ZMod 3) (i : ZMod 3) (f g : X → ℝ) :
    part c i (fun x => f x + g x) = fun x => part c i f x + part c i g x := by
  funext x
  simp only [part]
  split_ifs <;> simp

omit [Fintype X] in
theorem part_scale (c : X → ZMod 3) (i : ZMod 3) (a : ℝ) (f : X → ℝ) :
    part c i (fun x => a * f x) = fun x => a * part c i f x := by
  funext x
  simp only [part]
  split_ifs <;> simp

theorem part_comp_cycle (c : X → ZMod 3) (e : X ≃ X)
    (he : ∀ x, c (e x) = c x + 1) (i : ZMod 3) (f : X → ℝ) :
    size (part c i (fun x => f (e x))) = size (part c (i + 1) f) := by
  have h : part c i (fun x => f (e x)) = fun x => part c (i + 1) f (e x) := by
    funext x
    simp [part, he]
  rw [h, comp]

theorem cycle_triangle (c : X → ZMod 3) (e : X ≃ X)
    (he : ∀ x, c (e x) = c x + 1) (p q : X → ℝ)
    (hrec : ∀ x, 4 * q x = q (e x) + p (e x)) (i : ZMod 3) :
    4 * size (part c i q) ≤ size (part c (i + 1) q) + size (part c (i + 1) p) := by
  calc
    _ = size (part c i (fun x => 4 * q x)) := by rw [part_scale, scale 4 (by norm_num)]
    _ = size (part c i (fun x => q (e x) + p (e x))) := by simp_rw [hrec]
    _ ≤ size (part c i (fun x => q (e x))) + size (part c i (fun x => p (e x))) := by
      rw [part_add]
      exact add_le _ _
    _ = _ := by rw [part_comp_cycle c e he, part_comp_cycle c e he]

/-- A three-class overlap estimate. The zero class and the factor-two class
norm are essential hypotheses, not consequences for an arbitrary input. -/
theorem three_class_overlap (c : X → ZMod 3) (e : X ≃ X)
    (he : ∀ x, c (e x) = c x + 1) (p q : X → ℝ)
    (hrec : ∀ x, 4 * q x = q (e x) + p (e x))
    (hz : ∀ x, c x = 0 → p x = 0)
    (htwo : size (part c 2 p) = 2 * size (part c 1 p)) :
    7 * (∑ x, q x * p x) ≤ ∑ x, p x ^ 2 := by
  have hpzero : part c 0 p = fun _ => 0 := by
    funext x
    simp only [part]
    split_ifs with h
    · exact hz x h
    · rfl
  have hsizezero : size (part c 0 p) = 0 := by
    rw [hpzero]
    exact norm_zero (E := EuclideanSpace ℝ X)
  have h0 := cycle_triangle c e he p q hrec 0
  have h1 := cycle_triangle c e he p q hrec 1
  have h2 := cycle_triangle c e he p q hrec 2
  norm_num at h0 h1 h2
  rw [show (3 : ZMod 3) = 0 by decide] at h2
  rw [htwo] at h1
  rw [hsizezero] at h2
  have hb1 : 63 * size (part c 1 q) ≤ 33 * size (part c 1 p) := by linarith
  have hb2 : 63 * size (part c 2 q) ≤ 6 * size (part c 1 p) := by linarith
  have hdot : (∑ x, q x * p x) =
      (∑ x, part c 1 q x * part c 1 p x) + (∑ x, part c 2 q x * part c 2 p x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    have hc : ∀ z : ZMod 3, z = 0 ∨ z = 1 ∨ z = 2 := by decide
    rcases hc (c x) with h | h | h <;>
      simp [part, h, hz x, (by decide : (1 : ZMod 3) ≠ 2), (by decide : (2 : ZMod 3) ≠ 1)]
  have hsq : (∑ x, p x ^ 2) = size (part c 1 p) ^ 2 + size (part c 2 p) ^ 2 := by
    rw [sq_eq, sq_eq, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    have hc : ∀ z : ZMod 3, z = 0 ∨ z = 1 ∨ z = 2 := by decide
    rcases hc (c x) with h | h | h <;>
      simp [part, h, hz x, (by decide : (1 : ZMod 3) ≠ 2), (by decide : (2 : ZMod 3) ≠ 1)]
  rw [hdot, hsq, htwo]
  have hd1 := dot_le (part c 1 q) (part c 1 p)
  have hd2 := dot_le (part c 2 q) (part c 2 p)
  rw [htwo] at hd2
  have ha := nonneg (part c 1 p)
  nlinarith [mul_le_mul_of_nonneg_right hb1 ha, mul_le_mul_of_nonneg_right hb2 ha]

end FiniteL2

def residueThree (n : ℕ) : ZMod (3 ^ (n + 1)) →+* ZMod 3 :=
  ZMod.castHom (dvd_pow_self 3 (by omega : n + 1 ≠ 0)) (ZMod 3)

@[simp] theorem residueThree_natCast (n k : ℕ) :
    residueThree n (k : ZMod (3 ^ (n + 1))) = (k : ZMod 3) := by
  exact ZMod.cast_natCast (dvd_pow_self 3 (by omega : n + 1 ≠ 0)) k

theorem residueThree_val (n : ℕ) (x : ZMod (3 ^ (n + 1))) :
    (residueThree n x).val = x.val % 3 := by
  have h : residueThree n x = (x.val : ZMod 3) := by
    simpa only [ZMod.natCast_zmod_val] using residueThree_natCast n x.val
  rw [h, ZMod.val_natCast]

theorem lift_covers_class_one (n : ℕ) (x : ZMod (3 ^ (n + 1)))
    (hx : residueThree n x = 1) : ∃ y : ZMod (3 ^ n), lift n y = x := by
  have hv : x.val % 3 = 1 := by
    have h := congrArg ZMod.val hx
    rw [residueThree_val] at h
    exact h
  have hlt : x.val / 3 < 3 ^ n := by
    have h : x.val < 3 ^ n * 3 := by simpa only [pow_succ] using ZMod.val_lt x
    omega
  refine ⟨(x.val / 3 : ℕ), ?_⟩
  simp only [lift, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  have he : 3 * (x.val / 3) + 1 = x.val := by omega
  calc
    _ = ((3 * (x.val / 3) + 1 : ℕ) : ZMod (3 ^ (n + 1))) := by push_cast; rfl
    _ = x := by rw [he, ZMod.natCast_zmod_val]

theorem three_mul_val_cast (n k : ℕ) :
    (3 : ZMod (3 ^ (n + 1))) * ((k : ZMod (3 ^ n)).val : ZMod (3 ^ (n + 1))) =
      3 * (k : ZMod (3 ^ (n + 1))) := by
  rw [ZMod.val_natCast]
  have hzero : (3 : ZMod (3 ^ (n + 1))) * 3 ^ n = 0 := by
    have hs : ((3 ^ (n + 1) : ℕ) : ZMod (3 ^ (n + 1))) = 0 := ZMod.natCast_self _
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, pow_succ'] using hs
  have h := congrArg (fun a : ℕ => (a : ZMod (3 ^ (n + 1)))) (Nat.mod_add_div k (3 ^ n))
  push_cast at h
  calc
    _ = (3 : ZMod (3 ^ (n + 1))) *
        (((k % 3 ^ n : ℕ) : ZMod (3 ^ (n + 1))) + 3 ^ n * (k / 3 ^ n : ℕ)) := by
      rw [mul_add, ← mul_assoc, hzero, zero_mul, add_zero]
    _ = _ := by rw [h]

theorem lift_affine_four (n : ℕ) (y : ZMod (3 ^ n)) :
    lift n (4 * y + 1) = 4 * lift n y := by
  have h : 4 * y + 1 = ((4 * y.val + 1 : ℕ) : ZMod (3 ^ n)) := by simp
  rw [h]
  unfold lift
  rw [three_mul_val_cast]
  push_cast
  ring

theorem pmf_affine_four_recurrence (n : ℕ) (y : ZMod (3 ^ n)) :
    4 * (Tao.syracPMF (n + 1) (lift n y)).toReal =
      (Tao.syracPMF (n + 1) (lift n (4 * y + 1))).toReal +
        (Tao.syracPMF n (4 * y + 1)).toReal := by
  have hi := Tao.taoZModThreePow_inv_two_pow_mul (n + 1) 1
  simp only [pow_one] at hi
  have hh : half n (lift n (4 * y + 1)) = 2 * lift n y := by
    rw [lift_affine_four]
    unfold half
    calc
      _ = (2⁻¹ * 2) * (2 * lift n y) := by ring
      _ = _ := by rw [hi, one_mul]
  have h := pmf_half_recurrence n (lift n (4 * y + 1))
  rw [hh, pmf_two_lift, inputMass_lift] at h
  linarith

theorem inv_four_mul (n : ℕ) : (4 : ZMod (3 ^ n))⁻¹ * 4 = 1 := by
  have h := Tao.taoZModThreePow_inv_two_pow_mul n 2
  norm_num at h
  exact h

def affineFourEquiv (n : ℕ) : ZMod (3 ^ n) ≃ ZMod (3 ^ n) where
  toFun y := 4 * y + 1
  invFun y := 4⁻¹ * (y - 1)
  left_inv y := by simp [← mul_assoc, inv_four_mul]
  right_inv y := by
    have hi : (4 : ZMod (3 ^ n)) * 4⁻¹ = 1 := by rw [mul_comm, inv_four_mul]
    simp [← mul_assoc, hi]

def doubleEquiv (n : ℕ) : ZMod (3 ^ n) ≃ ZMod (3 ^ n) where
  toFun y := 2 * y
  invFun y := 2⁻¹ * y
  left_inv y := by
    have hi := Tao.taoZModThreePow_inv_two_pow_mul n 1
    simp only [pow_one] at hi
    simp [← mul_assoc, hi]
  right_inv y := by
    have hi := Tao.taoZModThreePow_inv_two_pow_mul n 1
    simp only [pow_one] at hi
    have hi' : (2 : ZMod (3 ^ n)) * 2⁻¹ = 1 := by rw [mul_comm, hi]
    simp [← mul_assoc, hi']

theorem residueThree_affine_four (n : ℕ) (y : ZMod (3 ^ (n + 1))) :
    residueThree n (affineFourEquiv (n + 1) y) = residueThree n y + 1 := by
  change residueThree n (4 * y + 1) = _
  rw [map_add, map_mul, map_one]
  have h4 : residueThree n (4 : ZMod (3 ^ (n + 1))) = 1 := by
    rw [show (4 : ZMod (3 ^ (n + 1))) = (4 : ℕ) by rfl, residueThree_natCast]
    decide
  rw [h4, one_mul]

theorem syracPMF_zero_class (n : ℕ) (x : ZMod (3 ^ (n + 1)))
    (hx : residueThree n x = 0) : (Tao.syracPMF (n + 1) x).toReal = 0 := by
  have hv : x.val % 3 = 0 := by
    have h := congrArg ZMod.val hx
    rw [residueThree_val] at h
    exact h
  simpa only [ZMod.natCast_zmod_val] using
    ND.PositiveDensity.syracPMF_natCast_toReal_eq_zero_of_mod_three_zero (by omega : 0 < n + 1) hv

theorem syracPMF_class_two_norm (n : ℕ) :
    FiniteL2.size (FiniteL2.part (residueThree n) 2 (fun x => (Tao.syracPMF (n + 1) x).toReal)) =
      2 * FiniteL2.size (FiniteL2.part (residueThree n) 1 (fun x => (Tao.syracPMF (n + 1) x).toReal)) := by
  let p := fun x => (Tao.syracPMF (n + 1) x).toReal
  have he : ∀ x : ZMod (3 ^ (n + 1)),
      residueThree n (doubleEquiv (n + 1) x) = 2 ↔ residueThree n x = 1 := by
    intro x
    change residueThree n (2 * x) = 2 ↔ _
    rw [map_mul]
    have h2 : residueThree n (2 : ZMod (3 ^ (n + 1))) = 2 := residueThree_natCast n 2
    rw [h2]
    have h : ∀ z : ZMod 3, 2 * z = 2 ↔ z = 1 := by decide
    exact h _
  have hfun : (fun x => FiniteL2.part (residueThree n) 2 p (doubleEquiv (n + 1) x)) =
      fun x => 2 * FiniteL2.part (residueThree n) 1 p x := by
    funext x
    simp only [FiniteL2.part]
    rw [if_congr (he x) rfl rfl]
    split_ifs with hx
    · obtain ⟨y, rfl⟩ := lift_covers_class_one n x hx
      exact pmf_two_lift n y
    · simp
  have hn := FiniteL2.comp (doubleEquiv (n + 1)) (FiniteL2.part (residueThree n) 2 p)
  rw [hfun, FiniteL2.scale 2 (by norm_num)] at hn
  exact hn.symm

/-- The actual overlap term is at most one seventh of the input square mass
at every positive input depth. -/
theorem syrac_overlap_le_seventh (n : ℕ) :
    7 * (∑ y : ZMod (3 ^ (n + 1)),
      (Tao.syracPMF (n + 1 + 1) (lift (n + 1) y)).toReal *
        (Tao.syracPMF (n + 1) y).toReal) ≤
      ∑ y : ZMod (3 ^ (n + 1)), (Tao.syracPMF (n + 1) y).toReal ^ 2 := by
  exact FiniteL2.three_class_overlap (residueThree n) (affineFourEquiv (n + 1))
    (residueThree_affine_four n)
    (fun y => (Tao.syracPMF (n + 1) y).toReal)
    (fun y => (Tao.syracPMF (n + 1 + 1) (lift (n + 1) y)).toReal)
    (pmf_affine_four_recurrence (n + 1)) (syracPMF_zero_class n) (syracPMF_class_two_norm n)

theorem collisionEnergy_step_le_nine_sevenths (n : ℕ) (hn : 1 ≤ n) :
    collisionEnergy (n + 1) ≤ (9 / 7 : ℝ) * collisionEnergy n := by
  cases n with
  | zero => omega
  | succ n =>
    have h := mul_le_mul_of_nonneg_left (syrac_overlap_le_seventh n)
      (show (0 : ℝ) ≤ 3 ^ (n + 1) by positivity)
    rw [collisionEnergy_recurrence]
    unfold collisionEnergy
    nlinarith

theorem collisionEnergy_succ_le_nine_sevenths_pow (n : ℕ) :
    collisionEnergy (n + 1) ≤ (5 / 3 : ℝ) * (9 / 7 : ℝ) ^ n := by
  induction n with
  | zero =>
    simpa using collisionEnergy_le_five_thirds_pow 1
  | succ n ih =>
    calc
      collisionEnergy (n + 1 + 1) ≤ (9 / 7 : ℝ) * collisionEnergy (n + 1) :=
        collisionEnergy_step_le_nine_sevenths (n + 1) (by omega)
      _ ≤ (9 / 7 : ℝ) * ((5 / 3 : ℝ) * (9 / 7 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

theorem collisionEnergy_le_nine_sevenths_pow (n : ℕ) :
    collisionEnergy n ≤ (35 / 27 : ℝ) * (9 / 7 : ℝ) ^ n := by
  cases n with
  | zero => rw [collisionEnergy_zero]; norm_num
  | succ n =>
    have h := collisionEnergy_succ_le_nine_sevenths_pow n
    rw [pow_succ]
    convert h using 1
    ring

end
end CollatzTargetDensity.SyracuseEnergy

namespace CollatzTargetDensity
open Erdos1135 SyracuseEnergy
noncomputable section

/-- The residue-class energy estimate in the ordinary predecessor count.
The loss remains exponential in the depth parameter. -/
theorem nine_sevenths_target_density (A : ℕ) (hA : 1 ≤ A) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ d : ℝ, 0 < d ∧
      ∀ a : ℕ, 0 < a → a % 3 ≠ 0 →
      ∀ t : ℕ, 1 ≤ t → a ≤ t ^ A →
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        d / ((a : ℝ) ^ 2 * (9 / 7 : ℝ) ^ (K * t)) * (X : ℝ) ≤ countBelow a X := by
  obtain ⟨K, hK, d, hd, hcount⟩ := energy_target_density A hA
  refine ⟨K, hK, (27 / 35 : ℝ) * d, by positivity, ?_⟩
  intro a ha hthree t ht hat
  obtain ⟨X₀, hX₀⟩ := hcount a ha hthree t ht hat
  refine ⟨X₀, ?_⟩
  intro X hX
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hE := collisionEnergy_pos (K * t)
  have hcoeff : d / ((a : ℝ) ^ 2 * ((35 / 27 : ℝ) * (9 / 7 : ℝ) ^ (K * t))) ≤
      d / ((a : ℝ) ^ 2 * collisionEnergy (K * t)) := by
    exact div_le_div_of_nonneg_left hd.le (by positivity)
      (mul_le_mul_of_nonneg_left (collisionEnergy_le_nine_sevenths_pow (K * t)) (sq_nonneg _))
  have heq : (27 / 35 : ℝ) * d / ((a : ℝ) ^ 2 * (9 / 7 : ℝ) ^ (K * t)) =
      d / ((a : ℝ) ^ 2 * ((35 / 27 : ℝ) * (9 / 7 : ℝ) ^ (K * t))) := by ring
  rw [heq]
  exact (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg X)).trans (hX₀ X hX)

end
end CollatzTargetDensity
