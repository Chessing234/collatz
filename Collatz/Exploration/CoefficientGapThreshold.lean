import Collatz.Exploration.ProductThresholds
import Collatz.Exploration.FloorBudgetComparison
import Collatz.Strategy.FirstLightDescent

/-! A linear sufficient source-floor threshold for each light coefficient pair.
These are conditional descent tools based on classical Bernoulli bounds. -/
namespace Collatz.Exploration.CoefficientGapThreshold
open FloorAffineError FloorProductError ProductThresholds FloorBudgetComparison

/-- A scalar margin implies the full powered product test. -/
theorem passes_of_scalar {C D k b : Nat}
    (hc : C*weight b < D*(weight b-k)) : Passes C D k b := by
  have hw : 0 < weight b^k := Nat.pow_pos (by unfold weight; omega)
  have h1 := Nat.mul_lt_mul_of_pos_right hc hw
  have h2 := Nat.mul_le_mul_left D (ratio_comparison b k)
  simp only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] at h1 h2
  have hh : (C*weight b^k)*weight b < (D*base b^k)*weight b := by
    simp only [Nat.mul_left_comm,Nat.mul_comm]
    omega
  exact Nat.lt_of_mul_lt_mul_right hh

/-- The required floor weight scales with odd count and reciprocal coefficient gap. -/
theorem passes_of_gap {C D k b : Nat} (hl : C ≤ D)
    (hg : k*D < (D-C)*weight b) : Passes C D k b := by
  apply passes_of_scalar
  have he : (D-C)*weight b = D*weight b-C*weight b := Nat.sub_mul _ _ _
  have hm : D*(weight b-k) = D*weight b-D*k := Nat.mul_sub _ _ _
  have hc := Nat.mul_le_mul_right (weight b) hl
  rw [he] at hg
  rw [hm]
  have hk : k*D=D*k := Nat.mul_comm _ _
  omega

/-- Gap-specific scalar source thresholds certify descent, with no individual trace products. -/
theorem descent_of_gap {n j : Nat} (hn : 0 < n)
    (hl : 3^oddCount n j ≤ 2^j)
    (hg : oddCount n j*2^j < (2^j-3^oddCount n j)*weight n) :
    ∃ i, i ≤ j ∧ acceleratedOrbit i n < n := by
  apply FloorProductDescent.descent_before hn
  exact passes_of_gap hl hg

/-- Improve the existing H*3^H cutoff using the first-light accumulator bound. -/
theorem first_light_below_horizon {H n j : Nat} (hj : j ≤ H)
    (hn : H*2^H < 3*n)
    (hf : FirstLightDescent.FirstLight n j) : acceleratedOrbit j n < n := by
  by_cases hd : acceleratedOrbit j n < n
  · exact hd
  · have hb := FirstLightDescent.failure_bound hf (by omega)
    have ha := Nat.le_trans (AffineExact.oddCount_le_self n j) hj
    have hp : 3^oddCount n j ≤ 2^H := Nat.le_trans (Nat.le_of_lt hf.1)
      (Nat.pow_le_pow_right (by decide) hj)
    have hm := Nat.mul_le_mul ha hp
    have hg : 1 ≤ 2^j-3^oddCount n j := by have := hf.1; omega
    have hl := Nat.mul_le_mul_left (3*n) hg
    simp only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] at hl hb
    omega

end Collatz.Exploration.CoefficientGapThreshold
