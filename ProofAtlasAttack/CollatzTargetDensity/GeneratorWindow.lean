import CollatzTargetDensity.GeneratorCostTail

/-! Exact finite-window recursion. No asymptotic coefficient claim is assumed. -/
namespace CollatzTargetDensity.GeneratorCostTail
open Erdos1135 FixedCostGenerators
open scoped BigOperators
noncomputable section

def cutoffValue (p : Polynomial ℕ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (K + 1), (p.coeff k : ℝ) * (1 / 2 : ℝ) ^ k

theorem shortValue_eq_cutoffValue (n K : ℕ) (r : ZMod (3 ^ n)) :
    shortValue n K r = cutoffValue (generator n r) K := by
  classical
  unfold shortValue cutoffValue
  rw [← Finset.sum_filter]
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at *
    omega
  · intro k _ hk
    have hcoeff : (generator n r).coeff k = 0 := by
      by_contra hc
      exact hk (by simp_all [Polynomial.mem_support_iff])
    simp [hcoeff]

theorem cutoffValue_nonneg (p : Polynomial ℕ) (K : ℕ) : 0 ≤ cutoffValue p K := by
  unfold cutoffValue
  exact Finset.sum_nonneg (fun _ _ => by positivity)

@[simp] theorem cutoffValue_zero (K : ℕ) : cutoffValue 0 K = 0 := by
  simp [cutoffValue]

@[simp] theorem cutoffValue_one (K : ℕ) : cutoffValue 1 K = 1 := by
  simp [cutoffValue, Polynomial.coeff_one]

theorem cutoffValue_sum {ι : Type*} (s : Finset ι) (p : ι → Polynomial ℕ) (K : ℕ) :
    cutoffValue (∑ i ∈ s, p i) K = ∑ i ∈ s, cutoffValue (p i) K := by
  simp only [cutoffValue, Polynomial.finset_sum_coeff, Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem cutoffValue_X_pow_mul (p : Polynomial ℕ) (j K : ℕ) :
    cutoffValue (Polynomial.X ^ j * p) K =
      if j ≤ K then (1 / 2 : ℝ) ^ j * cutoffValue p (K - j) else 0 := by
  classical
  by_cases hj : j ≤ K
  · rw [if_pos hj]
    unfold cutoffValue
    have hK : K + 1 = j + (K - j + 1) := by omega
    rw [hK, Finset.sum_range_add]
    have hz : (∑ k ∈ Finset.range j,
        ((Polynomial.X ^ j * p).coeff k : ℝ) * (1 / 2 : ℝ) ^ k) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hkj : ¬ j ≤ k := by simpa using Finset.mem_range.mp hk
      simp [Polynomial.coeff_X_pow_mul', hkj]
    rw [hz, zero_add, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp [Polynomial.coeff_X_pow_mul', pow_add]
    ring
  · rw [if_neg hj]
    unfold cutoffValue
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : ¬ j ≤ k := by have := Finset.mem_range.mp hk; omega
    simp [Polynomial.coeff_X_pow_mul', hkj]

theorem shortValue_zero (K : ℕ) (r : ZMod (3 ^ 0)) : shortValue 0 K r = 1 := by
  rw [shortValue_eq_cutoffValue]
  simp [generator]

theorem shortValue_nonneg (n K : ℕ) (r : ZMod (3 ^ n)) : 0 ≤ shortValue n K r := by
  rw [shortValue_eq_cutoffValue]
  exact cutoffValue_nonneg _ _

/-- Exact recursion with both the period and total-cost restrictions retained. -/
theorem shortValue_succ (n K : ℕ) (r : ZMod (3 ^ (n + 1))) :
    shortValue (n + 1) K r = ∑ j ∈ Finset.range (period n),
      if j ≤ K then (1 / 2 : ℝ) ^ j *
        (let s : ZMod (3 ^ (n + 1)) := 2 ^ (j + 1) * r
         if s.val % 3 = 1 then shortValue n (K - j) ((s.val / 3 : ℕ) : ZMod (3 ^ n))
         else 0)
      else 0 := by
  rw [shortValue_eq_cutoffValue, generator, cutoffValue_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [cutoffValue_X_pow_mul]
  split_ifs with hj
  · rw [polynomialBoundary_explicit]
    dsimp only
    split_ifs <;> simp [shortValue_eq_cutoffValue]
  · rfl

end
end CollatzTargetDensity.GeneratorCostTail
