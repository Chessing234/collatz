import Mathlib.Tactic

/-!
Finite arithmetic of near returns in the complementary Collatz recurrence.
All results below concern a finite recurrence only.  No infinite orbit,
summability hypothesis, or Collatz conjecture is used.
-/

namespace CollatzTargetDensity.ShadowReturnArithmetic

def blockProduct (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => blockProduct c k * c k

def blockOffset (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 3 * blockOffset c k + blockProduct c k

theorem blockProduct_pos (c : ℕ → ℕ) (L : ℕ)
    (hc : ∀ i < L, 1 ≤ c i) : 1 ≤ blockProduct c L := by
  induction L with
  | zero => simp [blockProduct]
  | succ L ih =>
    have hp := ih (fun i hi => hc i (by omega))
    have hlast := hc L (by omega)
    simp only [blockProduct]
    nlinarith

theorem blockProduct_le (c : ℕ → ℕ) (L C : ℕ)
    (hc : ∀ i < L, c i ≤ C) : blockProduct c L ≤ C ^ L := by
  induction L with
  | zero => simp [blockProduct]
  | succ L ih =>
    simpa only [blockProduct, pow_succ] using
      Nat.mul_le_mul (ih (fun i hi => hc i (by omega))) (hc L (by omega))

theorem blockOffset_pos (c : ℕ → ℕ) (L : ℕ) (hL : 0 < L)
    (hc : ∀ i < L, 1 ≤ c i) : 1 ≤ blockOffset c L := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  have hp := blockProduct_pos c k (fun i hi => hc i (by omega))
  simp only [blockOffset]
  omega

theorem block_identity (E : ℕ → ℝ) (c : ℕ → ℕ) (L : ℕ)
    (hstep : ∀ i < L, (c i : ℝ) * E (i + 1) = 3 * E i - 1) :
    (blockProduct c L : ℝ) * E L = (3 : ℝ) ^ L * E 0 - blockOffset c L := by
  induction L with
  | zero => simp [blockProduct, blockOffset]
  | succ L ih =>
    have hi := ih (fun i hi => hstep i (by omega))
    have hs := hstep L (by omega)
    have hm := congrArg (fun z : ℝ => (blockProduct c L : ℝ) * z) hs
    simp only [blockProduct, blockOffset, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
      pow_succ]
    nlinarith

/-- A close return anywhere in a short complementary-recurrence block forces
the initial value close to an integer divided by a *small* positive integer.
The denominator is at most `3 ^ r`, independent of the coefficient bound `C`.
The coefficient bound enters only through the approximation error. -/
theorem near_return_integer_anchor (E : ℕ → ℝ) (c : ℕ → ℕ)
    (r j p C : ℕ) (hp : 0 < p) (hjp : j + p ≤ r) (hC : 1 ≤ C)
    (hc : ∀ i < r, 1 ≤ c i ∧ c i ≤ C)
    (hstep : ∀ i < r, (c i : ℝ) * E (i + 1) = 3 * E i - 1)
    (hlow : 1 ≤ E j) {η : ℝ} (hη : 0 ≤ η)
    (hsmall : (C : ℝ) ^ r * η < 1)
    (hclose : |E (j + p) - E j| ≤ η) :
    ∃ q m : ℕ, 0 < q ∧ q ≤ 3 ^ r ∧
      |(q : ℝ) * E 0 - (m : ℝ)| ≤ (C : ℝ) ^ r * η := by
  let d : ℕ → ℕ := fun i => c (j + i)
  have hjr : j ≤ r := by omega
  have hpr : p ≤ r := by omega
  have hdpos : ∀ i < p, 1 ≤ d i := by
    intro i hi
    exact (hc (j + i) (by omega)).1
  have hdupper : ∀ i < p, d i ≤ C := by
    intro i hi
    exact (hc (j + i) (by omega)).2
  have hP := blockProduct_le c j C (fun i hi => (hc i (by omega)).2)
  have hD := blockProduct_le d p C hdupper
  have hR := blockOffset_pos d p hp hdpos
  have hblock := block_identity (fun i => E (j + i)) d p (by
    intro i hi
    simpa only [d, Nat.add_assoc] using hstep (j + i) (by omega))
  have hpre := block_identity E c j (fun i hi => hstep i (by omega))
  simp only [Nat.add_zero] at hblock
  have hCr : C ^ p ≤ C ^ r := Nat.pow_le_pow_right (by omega) hpr
  have hDC : (blockProduct d p : ℝ) ≤ (C : ℝ) ^ r := by
    exact_mod_cast hD.trans hCr
  have hDCη := mul_le_mul_of_nonneg_right hDC hη
  have hclose' := (abs_le.mp hclose).1
  have hdiff : blockProduct d p < 3 ^ p := by
    by_contra! hge
    have hgeR : (3 : ℝ) ^ p ≤ (blockProduct d p : ℝ) := by exact_mod_cast hge
    have hRreal : (1 : ℝ) ≤ blockOffset d p := by exact_mod_cast hR
    have hEj : 0 ≤ E j := by linarith
    have hmul := mul_le_mul_of_nonneg_right hgeR hEj
    have hclosemul := mul_le_mul_of_nonneg_left hclose'
      (Nat.cast_nonneg (blockProduct d p) : (0 : ℝ) ≤ blockProduct d p)
    nlinarith
  let D : ℕ := 3 ^ p - blockProduct d p
  have hDpos : 0 < D := by dsimp [D]; omega
  have hDle : D ≤ 3 ^ p := by dsimp [D]; omega
  have hDreal : (D : ℝ) = (3 : ℝ) ^ p - blockProduct d p := by
    dsimp [D]
    rw [Nat.cast_sub hdiff.le, Nat.cast_pow, Nat.cast_ofNat]
  let q : ℕ := 3 ^ j * D
  let m : ℕ := blockProduct c j * blockOffset d p + D * blockOffset c j
  have hqpos : 0 < q := Nat.mul_pos (by positivity) hDpos
  have hqlim : q ≤ 3 ^ r := by
    calc
      q ≤ 3 ^ j * 3 ^ p := Nat.mul_le_mul_left _ hDle
      _ = 3 ^ (j + p) := (pow_add _ _ _).symm
      _ ≤ 3 ^ r := Nat.pow_le_pow_right (by decide) hjp
  have hprod : blockProduct c j * blockProduct d p ≤ C ^ r := by
    calc
      _ ≤ C ^ j * C ^ p := Nat.mul_le_mul hP hD
      _ = C ^ (j + p) := (pow_add _ _ _).symm
      _ ≤ C ^ r := Nat.pow_le_pow_right (by omega) hjp
  have hprodR : (blockProduct c j : ℝ) * (blockProduct d p : ℝ) ≤ (C : ℝ) ^ r := by
    exact_mod_cast hprod
  have hid : (q : ℝ) * E 0 - (m : ℝ) =
      (blockProduct c j : ℝ) * (blockProduct d p : ℝ) * (E (j + p) - E j) := by
    dsimp [q, m]
    push_cast
    rw [hDreal]
    have hb := congrArg (fun z : ℝ => (blockProduct c j : ℝ) * z) hblock
    have hh := congrArg (fun z : ℝ => ((3 : ℝ) ^ p - blockProduct d p) * z) hpre
    nlinarith
  refine ⟨q, m, hqpos, hqlim, ?_⟩
  rw [hid, abs_mul, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ (blockProduct c j : ℝ) * (blockProduct d p : ℝ))]
  exact (mul_le_mul_of_nonneg_left hclose (by positivity)).trans
    (mul_le_mul_of_nonneg_right hprodR hη)

end CollatzTargetDensity.ShadowReturnArithmetic
