import CollatzTargetDensity.SyracuseCylinderSpread

/-!
# Concentration in the actual Syracuse law

Repeated valuation one follows the compatible ternary residues of -1.
Its probability is at least 2^(-n), so the density relative to full Haar
grows at least as (3/2)^n. In particular neither a uniform upper density
bound nor a uniform cubic-moment bound is available. These are obstructions
to proposed proof strategies, not counterexamples to the Collatz conjecture.
-/

namespace CollatzTargetDensity.SyracuseConcentration
open Erdos1135 Erdos1135.ND.PositiveDensity SyracuseMinorant
open scoped BigOperators
noncomputable section

theorem syracStep_neg_one (n : ℕ) :
    Tao.syracStep n (-1) (1 : ℕ+) = -1 := by
  have hp : 0 < 3 ^ n := by positivity
  have hv : (-1 : ZMod (3 ^ n)).val = 3 ^ n - 1 := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    rw [hm, ZMod.val_neg_one]
    omega
  have hcast : (3 : ZMod (3 ^ (n + 1))) * (3 : ZMod (3 ^ (n + 1))) ^ n = 0 := by
    rw [← pow_succ']
    exact_mod_cast (ZMod.natCast_self (3 ^ (n + 1)))
  have hinv := Tao.taoZModThreePow_inv_two_pow_mul (n + 1) 1
  simp only [pow_one] at hinv
  unfold Tao.syracStep
  simp only [PNat.val_ofNat, pow_one, hv, Nat.cast_sub (by omega : 1 ≤ 3 ^ n),
    Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  calc
    (2 : ZMod (3 ^ (n + 1)))⁻¹ * (3 * (3 ^ n - 1) + 1) =
        (2 : ZMod (3 ^ (n + 1)))⁻¹ * (3 * 3 ^ n - 2) := by ring
    _ = -1 := by rw [hcast, zero_sub, mul_neg, hinv]

/-- A literal atom estimate for the imported PMF, at every conductor. -/
theorem neg_one_atom_lower (n : ℕ) :
    (1 / 2 : ℝ) ^ n ≤ (Tao.syracPMF n (-1)).toReal := by
  induction n with
  | zero =>
    have hz : (-1 : ZMod (3 ^ 0)) = 0 := by decide
    rw [hz, Tao.syracPMF_zero_apply_zero]
    norm_num
  | succ n ih =>
    have hs := syracPMF_single_reverse_le n (-1) (-1) (1 : ℕ+)
      (syracStep_neg_one n)
    simp only [PNat.val_ofNat, pow_one] at hs
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right ih (by norm_num)).trans hs

/-- Here the normalization is full Haar: f_n = 3^n μ_n, with mean one. -/
theorem neg_one_density_lower (n : ℕ) :
    (3 / 2 : ℝ) ^ n ≤ ndSyracuseUniformDensity n (-1) := by
  have hh := mul_le_mul_of_nonneg_left (neg_one_atom_lower n)
    (show (0 : ℝ) ≤ 3 ^ n by positivity)
  unfold ndSyracuseUniformDensity Tao.syracPMFMassVector
  push_cast
  convert hh using 1
  rw [← mul_pow]
  norm_num

theorem no_uniform_density_upper :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ r : ZMod (3 ^ n),
      ndSyracuseUniformDensity n r ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 3 / 2)
  have hp : (3 / 2 : ℝ) ^ n ≤ (3 / 2 : ℝ) ^ (n + 1) := by
    rw [pow_succ]
    nlinarith [show (0 : ℝ) ≤ (3 / 2 : ℝ) ^ n by positivity]
  exact (not_lt_of_ge ((neg_one_density_lower (n + 1)).trans
    (hC (n + 1) (by omega) (-1)))) (hn.trans_le hp)

def cubicMoment (n : ℕ) : ℝ :=
  (∑ r : ZMod (3 ^ n), (ndSyracuseUniformDensity n r) ^ 3) / (3 : ℝ) ^ n

theorem uniformDensity_nonneg (n : ℕ) (r : ZMod (3 ^ n)) :
    0 ≤ ndSyracuseUniformDensity n r := by
  unfold ndSyracuseUniformDensity Tao.syracPMFMassVector
  positivity

/-- A single exceptional atom forces exponential growth of the third moment. -/
theorem cubicMoment_lower (n : ℕ) : (9 / 8 : ℝ) ^ n ≤ cubicMoment n := by
  classical
  have hsingle := Finset.single_le_sum
    (f := fun r : ZMod (3 ^ n) => (ndSyracuseUniformDensity n r) ^ 3)
    (fun r _ => pow_nonneg (uniformDensity_nonneg n r) 3)
    (Finset.mem_univ (-1 : ZMod (3 ^ n)))
  have hcube := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ n)
    (neg_one_density_lower n) 3
  unfold cubicMoment
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 3 ^ n)).2
  calc
    (9 / 8 : ℝ) ^ n * 3 ^ n = ((3 / 2 : ℝ) ^ n) ^ 3 := by
      rw [← mul_pow, pow_right_comm]
      norm_num
    _ ≤ _ := hcube.trans hsingle

theorem no_uniform_cubicMoment_upper :
    ¬ ∃ C : ℝ, ∀ n : ℕ, cubicMoment n ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 9 / 8)
  exact (not_lt_of_ge ((cubicMoment_lower n).trans (hC n))) hn

end
end CollatzTargetDensity.SyracuseConcentration
