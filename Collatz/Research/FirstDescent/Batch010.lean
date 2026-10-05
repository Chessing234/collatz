import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 10. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch010
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (13, 1567). -/
theorem data_13_1567 : oddCount 1567 13 = 8 ∧
    acceleratedOrbit 13 1567 = 1256 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_1567 : ∀ j : Fin 13,
    1567 ≤ acceleratedOrbit j.val 1567 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_1567 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 1567) = 6561 * m + 1256 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 1567
  rw [data_13_1567.1, data_13_1567.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_1567 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 1567) < 8192 * m + 1567 := by
  apply descent_of_endpoint
  · rw [data_13_1567.1]; exact data_13_1567.2.2
  · rw [data_13_1567.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 1727). -/
theorem data_13_1727 : oddCount 1727 13 = 8 ∧
    acceleratedOrbit 13 1727 = 1384 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_1727 : ∀ j : Fin 13,
    1727 ≤ acceleratedOrbit j.val 1727 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_1727 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 1727) = 6561 * m + 1384 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 1727
  rw [data_13_1727.1, data_13_1727.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_1727 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 1727) < 8192 * m + 1727 := by
  apply descent_of_endpoint
  · rw [data_13_1727.1]; exact data_13_1727.2.2
  · rw [data_13_1727.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 1983). -/
theorem data_13_1983 : oddCount 1983 13 = 8 ∧
    acceleratedOrbit 13 1983 = 1589 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_1983 : ∀ j : Fin 13,
    1983 ≤ acceleratedOrbit j.val 1983 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_1983 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 1983) = 6561 * m + 1589 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 1983
  rw [data_13_1983.1, data_13_1983.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_1983 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 1983) < 8192 * m + 1983 := by
  apply descent_of_endpoint
  · rw [data_13_1983.1]; exact data_13_1983.2.2
  · rw [data_13_1983.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 2015). -/
theorem data_13_2015 : oddCount 2015 13 = 8 ∧
    acceleratedOrbit 13 2015 = 1615 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_2015 : ∀ j : Fin 13,
    2015 ≤ acceleratedOrbit j.val 2015 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_2015 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 2015) = 6561 * m + 1615 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 2015
  rw [data_13_2015.1, data_13_2015.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_2015 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 2015) < 8192 * m + 2015 := by
  apply descent_of_endpoint
  · rw [data_13_2015.1]; exact data_13_2015.2.2
  · rw [data_13_2015.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 2075). -/
theorem data_13_2075 : oddCount 2075 13 = 8 ∧
    acceleratedOrbit 13 2075 = 1663 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_2075 : ∀ j : Fin 13,
    2075 ≤ acceleratedOrbit j.val 2075 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_2075 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 2075) = 6561 * m + 1663 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 2075
  rw [data_13_2075.1, data_13_2075.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_2075 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 2075) < 8192 * m + 2075 := by
  apply descent_of_endpoint
  · rw [data_13_2075.1]; exact data_13_2075.2.2
  · rw [data_13_2075.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 2079). -/
theorem data_13_2079 : oddCount 2079 13 = 8 ∧
    acceleratedOrbit 13 2079 = 1666 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_2079 : ∀ j : Fin 13,
    2079 ≤ acceleratedOrbit j.val 2079 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_2079 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 2079) = 6561 * m + 1666 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 2079
  rw [data_13_2079.1, data_13_2079.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_2079 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 2079) < 8192 * m + 2079 := by
  apply descent_of_endpoint
  · rw [data_13_2079.1]; exact data_13_2079.2.2
  · rw [data_13_2079.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 2095). -/
theorem data_13_2095 : oddCount 2095 13 = 8 ∧
    acceleratedOrbit 13 2095 = 1679 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_2095 : ∀ j : Fin 13,
    2095 ≤ acceleratedOrbit j.val 2095 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_2095 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 2095) = 6561 * m + 1679 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 2095
  rw [data_13_2095.1, data_13_2095.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_2095 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 2095) < 8192 * m + 2095 := by
  apply descent_of_endpoint
  · rw [data_13_2095.1]; exact data_13_2095.2.2
  · rw [data_13_2095.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 2271). -/
theorem data_13_2271 : oddCount 2271 13 = 8 ∧
    acceleratedOrbit 13 2271 = 1820 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_2271 : ∀ j : Fin 13,
    2271 ≤ acceleratedOrbit j.val 2271 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_2271 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 2271) = 6561 * m + 1820 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 2271
  rw [data_13_2271.1, data_13_2271.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_2271 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 2271) < 8192 * m + 2271 := by
  apply descent_of_endpoint
  · rw [data_13_2271.1]; exact data_13_2271.2.2
  · rw [data_13_2271.2.1]; decide

end Collatz.Research.FirstDescent.Batch010
