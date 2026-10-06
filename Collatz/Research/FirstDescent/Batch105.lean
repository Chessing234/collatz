import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 105. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch105
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 11375). -/
theorem data_18_11375 : oddCount 11375 18 = 11 ∧
    acceleratedOrbit 18 11375 = 7688 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_11375 : ∀ j : Fin 18,
    11375 ≤ acceleratedOrbit j.val 11375 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_11375 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 11375) = 177147 * m + 7688 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 11375
  rw [data_18_11375.1, data_18_11375.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_11375 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 11375) < 262144 * m + 11375 := by
  apply descent_of_endpoint
  · rw [data_18_11375.1]; exact data_18_11375.2.2
  · rw [data_18_11375.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 11423). -/
theorem data_18_11423 : oddCount 11423 18 = 11 ∧
    acceleratedOrbit 18 11423 = 7720 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_11423 : ∀ j : Fin 18,
    11423 ≤ acceleratedOrbit j.val 11423 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_11423 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 11423) = 177147 * m + 7720 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 11423
  rw [data_18_11423.1, data_18_11423.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_11423 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 11423) < 262144 * m + 11423 := by
  apply descent_of_endpoint
  · rw [data_18_11423.1]; exact data_18_11423.2.2
  · rw [data_18_11423.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 11455). -/
theorem data_18_11455 : oddCount 11455 18 = 11 ∧
    acceleratedOrbit 18 11455 = 7742 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_11455 : ∀ j : Fin 18,
    11455 ≤ acceleratedOrbit j.val 11455 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_11455 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 11455) = 177147 * m + 7742 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 11455
  rw [data_18_11455.1, data_18_11455.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_11455 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 11455) < 262144 * m + 11455 := by
  apply descent_of_endpoint
  · rw [data_18_11455.1]; exact data_18_11455.2.2
  · rw [data_18_11455.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 12059). -/
theorem data_18_12059 : oddCount 12059 18 = 11 ∧
    acceleratedOrbit 18 12059 = 8150 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_12059 : ∀ j : Fin 18,
    12059 ≤ acceleratedOrbit j.val 12059 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_12059 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 12059) = 177147 * m + 8150 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 12059
  rw [data_18_12059.1, data_18_12059.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_12059 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 12059) < 262144 * m + 12059 := by
  apply descent_of_endpoint
  · rw [data_18_12059.1]; exact data_18_12059.2.2
  · rw [data_18_12059.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 12199). -/
theorem data_18_12199 : oddCount 12199 18 = 11 ∧
    acceleratedOrbit 18 12199 = 8245 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_12199 : ∀ j : Fin 18,
    12199 ≤ acceleratedOrbit j.val 12199 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_12199 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 12199) = 177147 * m + 8245 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 12199
  rw [data_18_12199.1, data_18_12199.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_12199 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 12199) < 262144 * m + 12199 := by
  apply descent_of_endpoint
  · rw [data_18_12199.1]; exact data_18_12199.2.2
  · rw [data_18_12199.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 12479). -/
theorem data_18_12479 : oddCount 12479 18 = 11 ∧
    acceleratedOrbit 18 12479 = 8434 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_12479 : ∀ j : Fin 18,
    12479 ≤ acceleratedOrbit j.val 12479 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_12479 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 12479) = 177147 * m + 8434 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 12479
  rw [data_18_12479.1, data_18_12479.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_12479 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 12479) < 262144 * m + 12479 := by
  apply descent_of_endpoint
  · rw [data_18_12479.1]; exact data_18_12479.2.2
  · rw [data_18_12479.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 12591). -/
theorem data_18_12591 : oddCount 12591 18 = 11 ∧
    acceleratedOrbit 18 12591 = 8510 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_12591 : ∀ j : Fin 18,
    12591 ≤ acceleratedOrbit j.val 12591 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_12591 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 12591) = 177147 * m + 8510 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 12591
  rw [data_18_12591.1, data_18_12591.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_12591 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 12591) < 262144 * m + 12591 := by
  apply descent_of_endpoint
  · rw [data_18_12591.1]; exact data_18_12591.2.2
  · rw [data_18_12591.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 12831). -/
theorem data_18_12831 : oddCount 12831 18 = 11 ∧
    acceleratedOrbit 18 12831 = 8672 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_12831 : ∀ j : Fin 18,
    12831 ≤ acceleratedOrbit j.val 12831 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_12831 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 12831) = 177147 * m + 8672 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 12831
  rw [data_18_12831.1, data_18_12831.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_12831 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 12831) < 262144 * m + 12831 := by
  apply descent_of_endpoint
  · rw [data_18_12831.1]; exact data_18_12831.2.2
  · rw [data_18_12831.2.1]; decide

end Collatz.Research.FirstDescent.Batch105
