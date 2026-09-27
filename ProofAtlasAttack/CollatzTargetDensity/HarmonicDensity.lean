import CollatzTargetDensity.HarmonicTargets
import Mathlib.Data.Nat.Log

/-! A target-uniform lower logarithmic density, with a quadratic activation bound.
This is a predecessor theorem, not a proof that any target converges. -/
namespace CollatzTargetDensity.HarmonicTargets
open Erdos1135
open scoped BigOperators
noncomputable section

theorem logCount_prefix_mono (s : Set ℕ) {X Y : ℕ} (h : X ≤ Y) :
    Tao.logCount s X ≤ Tao.logCount s Y := by
  classical
  unfold Tao.logCount
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
    (fun _ _ _ => by split_ifs; exact (Tao.logWeight_pos _).le; exact le_rfl)

theorem log_sixty_four_le_six : Real.log 64 ≤ 6 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  have he : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
  rw [he]
  linarith

/-- An elementary interpolation lemma. The denominator is the actual harmonic
mass used by the imported logarithmic-density definition. -/
theorem ratio_lower_of_exponential_prefixes (s : Set ℕ) (B : ℕ) (hB : 0 < B)
    (c : ℝ) (hc : 0 ≤ c)
    (hcount : ∀ L : ℕ, (L + 1 : ℕ) * c ≤ Tao.logCount s (B * 64 ^ L)) :
    ∀ X : ℕ, B ^ 2 ≤ X → c / 13 ≤ Tao.logCountingRatio s X := by
  intro X hX
  have hXpos : 0 < X := (by positivity : 0 < B ^ 2).trans_le hX
  have hdiv : B ≤ X / B := (Nat.le_div_iff_mul_le hB).mpr (by simpa [pow_two] using hX)
  have hdivpos : 0 < X / B := hB.trans_le hdiv
  let q := Nat.log 64 (X / B)
  have hqlo : 64 ^ q ≤ X / B := Nat.pow_log_le_self 64 hdivpos.ne'
  have hqhi : X / B < 64 ^ (q + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hcut : B * 64 ^ q ≤ X := by
    have h := (Nat.le_div_iff_mul_le hB).mp hqlo
    simpa only [Nat.mul_comm] using h
  have hupper : X < B * 64 ^ (q + 1) := by
    have h := (Nat.div_lt_iff_lt_mul hB).mp hqhi
    simpa only [Nat.mul_comm] using h
  have hBupper : B < 64 ^ (q + 1) := hdiv.trans_lt hqhi
  have hXX : X < 64 ^ (2 * (q + 1)) := by
    have hmul : B * 64 ^ (q + 1) < 64 ^ (q + 1) * 64 ^ (q + 1) :=
      Nat.mul_lt_mul_of_pos_right hBupper (by positivity)
    simpa only [← pow_add, ← two_mul] using hupper.trans hmul
  have hlog : Real.log X ≤ (2 * (q + 1) : ℕ) * Real.log 64 := by
    have hxR : (0 : ℝ) < X := by exact_mod_cast hXpos
    have hbR : (X : ℝ) ≤ (64 : ℝ) ^ (2 * (q + 1)) := by exact_mod_cast hXX.le
    have hl := Real.log_le_log hxR hbR
    simpa only [Real.log_pow] using hl
  have hmass : Tao.logMass X ≤ 13 * (q + 1 : ℕ) := by
    have hh := harmonic_le_one_add_log X
    have hg := mul_le_mul_of_nonneg_left log_sixty_four_le_six
      (show (0 : ℝ) ≤ (2 * (q + 1) : ℕ) by positivity)
    rw [Tao.logMass_eq_harmonic]
    push_cast at hlog hg ⊢
    linarith
  have hlow := (hcount q).trans (logCount_prefix_mono s hcut)
  unfold Tao.logCountingRatio
  apply (le_div_iff₀ (Tao.logMass_pos hXpos)).mpr
  have hm := mul_le_mul_of_nonneg_left hmass (show (0 : ℝ) ≤ c / 13 by positivity)
  calc
    c / 13 * Tao.logMass X ≤ c / 13 * (13 * (q + 1 : ℕ)) := hm
    _ = (q + 1 : ℕ) * c := by ring
    _ ≤ _ := hlow

/-- There are absolute constants d > 0 and A ≥ 1 such that every target
prime to three has logarithmic predecessor ratio at least d/a at every
cutoff X ≥ (A*a)^2. No convergence or cycle-exclusion hypothesis is used. -/
theorem uniform_raw_logCountingRatio_lower :
    ∃ d : ℝ, 0 < d ∧ ∃ A : ℕ, 1 ≤ A ∧ ∀ a : ℕ, a % 3 ≠ 0 →
      ∀ X : ℕ, (A * a) ^ 2 ≤ X → d / a ≤ Tao.logCountingRatio (rawReaches a) X := by
  obtain ⟨d, hd, C, N, hC, hN, hcount⟩ := uniform_raw_logCount_lower
  let A := 2 ^ (6 * N) * C
  have hA : 1 ≤ A := by
    have hp : 1 ≤ 2 ^ (6 * N) := Nat.one_le_pow _ _ (by omega)
    dsimp [A]
    nlinarith
  refine ⟨d / 13, by positivity, A, hA, ?_⟩
  intro a ha X hX
  have hapos : 0 < a := by omega
  have hB : 0 < A * a := Nat.mul_pos (by omega) hapos
  have hpref (L : ℕ) : (L + 1 : ℕ) * (d / a) ≤
      Tao.logCount (rawReaches a) ((A * a) * 64 ^ L) := by
    have he : (A * a) * 64 ^ L = 2 ^ (6 * (N + L)) * (C * a) := by
      dsimp [A]
      rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_mul, Nat.mul_add, pow_add]
      ring
    rw [he]
    exact hcount a ha L
  have h := ratio_lower_of_exponential_prefixes (rawReaches a) (A * a) hB
    (d / a) (by positivity) hpref X hX
  convert h using 1
  ring

end
end CollatzTargetDensity.HarmonicTargets
