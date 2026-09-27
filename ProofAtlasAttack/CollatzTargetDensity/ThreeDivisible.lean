import CollatzTargetDensity.RawBridge
import Erdos1135.Terras.Density.NaturalDensity

/-! Exact predecessor structure for the excluded targets divisible by 3. -/
namespace CollatzTargetDensity
open Erdos1135

theorem reaches_three_divisible_iff {target n : ℕ} (hthree : target % 3 = 0) :
    Reaches n target ↔ ∃ k : ℕ, n = 2 ^ k * target := by
  constructor
  · rintro ⟨m, hm⟩
    induction m generalizing n with
    | zero => exact ⟨0, by simpa using hm⟩
    | succ m ih =>
      rw [Function.iterate_succ_apply] at hm
      obtain ⟨k, hk⟩ := ih hm
      have hstep : collatzStep n % 3 = 0 := by
        rw [hk, Nat.mul_mod, hthree]
        simp
      have he : Even n := by
        by_contra hne
        rw [collatzStep_eq_three_mul_add_one_of_not_even hne] at hstep
        omega
      have hmod := Nat.even_iff.mp he
      refine ⟨k + 1, ?_⟩
      calc
        n = 2 * (n / 2) := by omega
        _ = 2 * collatzStep n := by rw [collatzStep_eq_div_two_of_even he]
        _ = 2 * (2 ^ k * target) := by rw [hk]
        _ = 2 ^ (k + 1) * target := by rw [pow_succ]; ring
  · rintro ⟨k, rfl⟩
    exact Tao.reaches_powTwo_mul k target

theorem three_divisible_count_at_dyadic_cutoff {target : ℕ}
    (hpos : 0 < target) (hthree : target % 3 = 0) (k : ℕ) :
    Terras.natCount (rawReaches target) (2 ^ k * target) = k := by
  classical
  have hmono : StrictMono (fun j : ℕ => 2 ^ j * target) := by
    intro i j hij
    exact Nat.mul_lt_mul_of_pos_right
      ((Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).2 hij) hpos
  have hfilter : (Finset.range (2 ^ k * target)).filter (fun n => n ∈ rawReaches target) =
      (Finset.range k).image (fun j => 2 ^ j * target) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hnlt, hn⟩
      obtain ⟨j, hj⟩ := (reaches_three_divisible_iff hthree).1 hn.2
      refine ⟨j, ?_, hj.symm⟩
      rw [hj] at hnlt
      exact hmono.lt_iff_lt.mp hnlt
    · rintro ⟨j, hj, rfl⟩
      exact ⟨hmono hj, Nat.mul_pos (by positivity) hpos, Tao.reaches_powTwo_mul j target⟩
  unfold Terras.natCount
  rw [Nat.count_eq_card_filter_range, hfilter,
    Finset.card_image_of_injective _ hmono.injective, Finset.card_range]

theorem square_le_two_pow {k : ℕ} (hk : 4 ≤ k) : k ^ 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [pow_succ (2 : ℕ) k]
    nlinarith

theorem no_positive_lower_density_three_divisible {target : ℕ}
    (hpos : 0 < target) (hthree : target % 3 = 0) :
    ¬∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      c * (X : ℝ) ≤ (Terras.natCount (rawReaches target) X : ℝ) := by
  rintro ⟨c, hc, X₀, hX₀⟩
  obtain ⟨k, hk⟩ := exists_nat_gt (max ((max X₀ 4 : ℕ) : ℝ) (1 / c))
  have hknat : max X₀ 4 < k := by exact_mod_cast (le_max_left _ _).trans_lt hk
  have hk4 : 4 ≤ k := by omega
  have hck : 1 < (k : ℝ) * c :=
    (div_lt_iff₀ hc).1 ((le_max_right _ _).trans_lt hk)
  have hsquare : k ^ 2 ≤ 2 ^ k * target :=
    (square_le_two_pow hk4).trans (Nat.le_mul_of_pos_right _ hpos)
  have hroom : X₀ ≤ 2 ^ k * target := by
    have hk_le_square : k ≤ k ^ 2 := by nlinarith
    omega
  have hcount := hX₀ (2 ^ k * target) hroom
  rw [three_divisible_count_at_dyadic_cutoff hpos hthree k] at hcount
  have hsquare_real : (k : ℝ) ^ 2 ≤ ((2 ^ k * target : ℕ) : ℝ) := by
    exact_mod_cast hsquare
  have hpaid := mul_le_mul_of_nonneg_left hsquare_real hc.le
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  nlinarith

end CollatzTargetDensity
