import CollatzTargetDensity.FixedCostGenerators

/-!
Uniform control of large path costs in the finite generator law.
This retains a linear cost window. It does not establish a lower bound
at one specified cost or prove Collatz convergence.
-/
namespace CollatzTargetDensity.GeneratorCostTail
open Erdos1135 FixedCostGenerators Filter
open scoped BigOperators Topology
noncomputable section

def evalAt (z : ℝ) (n : ℕ) (r : ZMod (3 ^ n)) : ℝ :=
  (generator n r).eval₂ (Nat.castRingHom ℝ) z

theorem evalAt_succ (z : ℝ) (n : ℕ) (r : ZMod (3 ^ (n + 1))) :
    evalAt z (n + 1) r = ∑ j ∈ Finset.range (period n), z ^ j *
      (let s : ZMod (3 ^ (n + 1)) := 2 ^ (j + 1) * r
       if s.val % 3 = 1 then evalAt z n ((s.val / 3 : ℕ) : ZMod (3 ^ n)) else 0) := by
  unfold evalAt
  rw [generator]
  simp only [Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
    polynomialBoundary_explicit]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem geometric_three_quarters_sum_le (m : ℕ) :
    (∑ j ∈ Finset.range m, (3 / 4 : ℝ) ^ j) ≤ 4 := by
  have h := geom_sum_mul (3 / 4 : ℝ) m
  have hp : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ m := by positivity
  nlinarith

/-- A uniform exponential moment bound, with the residue retained. -/
theorem evalAt_three_quarters_le (n : ℕ) :
    ∀ r : ZMod (3 ^ n), evalAt (3 / 4) n r ≤ (4 : ℝ) ^ n := by
  induction n with
  | zero => intro r; simp [evalAt, generator]
  | succ n ih =>
    intro r
    rw [evalAt_succ]
    calc
      _ ≤ ∑ j ∈ Finset.range (period n), (3 / 4 : ℝ) ^ j * 4 ^ n := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp only
        split_ifs
        · exact ih _
        · positivity
      _ = (∑ j ∈ Finset.range (period n), (3 / 4 : ℝ) ^ j) * 4 ^ n := by
        rw [Finset.sum_mul]
      _ ≤ 4 * 4 ^ n :=
        mul_le_mul_of_nonneg_right (geometric_three_quarters_sum_le _) (by positivity)
      _ = 4 ^ (n + 1) := by rw [pow_succ]; ring

def shortValue (n K : ℕ) (r : ZMod (3 ^ n)) : ℝ :=
  ∑ k ∈ (generator n r).support,
    if k ≤ K then ((generator n r).coeff k : ℝ) * (1 / 2 : ℝ) ^ k else 0

def tailValue (n K : ℕ) (r : ZMod (3 ^ n)) : ℝ :=
  ∑ k ∈ (generator n r).support,
    if K < k then ((generator n r).coeff k : ℝ) * (1 / 2 : ℝ) ^ k else 0

theorem value_eq_short_add_tail (n K : ℕ) (r : ZMod (3 ^ n)) :
    value n r = shortValue n K r + tailValue n K r := by
  rw [value, Polynomial.eval₂_eq_sum]
  unfold Polynomial.sum shortValue tailValue
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k ≤ K <;> simp [hk, Nat.not_lt.mpr, Nat.lt_of_not_ge]

theorem half_pow_le_tilted {K k : ℕ} (hk : K ≤ k) :
    (1 / 2 : ℝ) ^ k ≤ (2 / 3 : ℝ) ^ K * (3 / 4 : ℝ) ^ k := by
  have h := mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
      (by norm_num : (2 / 3 : ℝ) ≤ 1) hk)
    (show (0 : ℝ) ≤ (3 / 4 : ℝ) ^ k by positivity)
  simpa only [← mul_pow, show (2 / 3 : ℝ) * (3 / 4) = 1 / 2 by norm_num] using h

theorem tailValue_le_tilted (n K : ℕ) (r : ZMod (3 ^ n)) :
    tailValue n K r ≤ (2 / 3 : ℝ) ^ K * evalAt (3 / 4) n r := by
  rw [evalAt, Polynomial.eval₂_eq_sum]
  unfold tailValue Polynomial.sum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : K < k
  · rw [if_pos hk]
    have h := mul_le_mul_of_nonneg_left (half_pow_le_tilted hk.le)
      (Nat.cast_nonneg ((generator n r).coeff k) : (0 : ℝ) ≤ _)
    convert h using 1
    simp
    ring
  · rw [if_neg hk]
    simpa using (show (0 : ℝ) ≤ (2 / 3 : ℝ) ^ K *
      (((generator n r).coeff k : ℝ) * (3 / 4 : ℝ) ^ k) by positivity)

/-- Costs above 5n have a uniformly exponentially small weighted mass. -/
theorem tailValue_five_mul_le (n : ℕ) (r : ZMod (3 ^ n)) :
    tailValue n (5 * n) r ≤ (128 / 243 : ℝ) ^ n := by
  have h := (tailValue_le_tilted n (5 * n) r).trans
    (mul_le_mul_of_nonneg_left (evalAt_three_quarters_le n r) (by positivity))
  convert h using 1
  rw [pow_mul, ← mul_pow]
  norm_num

/-- A fixed positive fraction of the uniform atom floor survives the cost
cutoff 5n, eventually with an onset independent of the target residue. -/
theorem eventually_shortValue_lower :
    ∃ d : ℝ, 0 < d ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ r : ZMod (3 ^ n), IsUnit r → d * (2 / 3 : ℝ) ^ n ≤ shortValue n (5 * n) r := by
  obtain ⟨c, hc, hfloor⟩ := uniform_generator_value_lower
  have ht : Tendsto (fun n : ℕ => (64 / 81 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsmall : ∀ᶠ n : ℕ in atTop, (64 / 81 : ℝ) ^ n < c / 2 :=
    (tendsto_order.mp ht).2 _ (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  refine ⟨c / 2, by positivity, max N 1, le_max_right _ _, ?_⟩
  intro n hn r hr
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hcn := hN n ((le_max_left _ _).trans hn)
  have htail := tailValue_five_mul_le n r
  have hsplit := value_eq_short_add_tail n (5 * n) r
  have hv := hfloor n hn1 r hr
  have he : (128 / 243 : ℝ) ^ n = (64 / 81 : ℝ) ^ n * (2 / 3 : ℝ) ^ n := by
    rw [← mul_pow]
    norm_num
  rw [he] at htail
  have hm := mul_le_mul_of_nonneg_right hcn.le
    (show (0 : ℝ) ≤ (2 / 3 : ℝ) ^ n by positivity)
  linarith

end
end CollatzTargetDensity.GeneratorCostTail
