import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 112. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch112
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 26855). -/
theorem data_18_26855 : oddCount 26855 18 = 11 ∧
    acceleratedOrbit 18 26855 = 18149 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_26855 : ∀ j : Fin 18,
    26855 ≤ acceleratedOrbit j.val 26855 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_26855 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 26855) = 177147 * m + 18149 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 26855
  rw [data_18_26855.1, data_18_26855.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_26855 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 26855) < 262144 * m + 26855 := by
  apply descent_of_endpoint
  · rw [data_18_26855.1]; exact data_18_26855.2.2
  · rw [data_18_26855.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 26943). -/
theorem data_18_26943 : oddCount 26943 18 = 11 ∧
    acceleratedOrbit 18 26943 = 18208 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_26943 : ∀ j : Fin 18,
    26943 ≤ acceleratedOrbit j.val 26943 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_26943 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 26943) = 177147 * m + 18208 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 26943
  rw [data_18_26943.1, data_18_26943.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_26943 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 26943) < 262144 * m + 26943 := by
  apply descent_of_endpoint
  · rw [data_18_26943.1]; exact data_18_26943.2.2
  · rw [data_18_26943.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 27295). -/
theorem data_18_27295 : oddCount 27295 18 = 11 ∧
    acceleratedOrbit 18 27295 = 18446 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_27295 : ∀ j : Fin 18,
    27295 ≤ acceleratedOrbit j.val 27295 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_27295 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 27295) = 177147 * m + 18446 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 27295
  rw [data_18_27295.1, data_18_27295.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_27295 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 27295) < 262144 * m + 27295 := by
  apply descent_of_endpoint
  · rw [data_18_27295.1]; exact data_18_27295.2.2
  · rw [data_18_27295.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 27375). -/
theorem data_18_27375 : oddCount 27375 18 = 11 ∧
    acceleratedOrbit 18 27375 = 18500 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_27375 : ∀ j : Fin 18,
    27375 ≤ acceleratedOrbit j.val 27375 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_27375 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 27375) = 177147 * m + 18500 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 27375
  rw [data_18_27375.1, data_18_27375.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_27375 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 27375) < 262144 * m + 27375 := by
  apply descent_of_endpoint
  · rw [data_18_27375.1]; exact data_18_27375.2.2
  · rw [data_18_27375.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 27455). -/
theorem data_18_27455 : oddCount 27455 18 = 11 ∧
    acceleratedOrbit 18 27455 = 18554 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_27455 : ∀ j : Fin 18,
    27455 ≤ acceleratedOrbit j.val 27455 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_27455 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 27455) = 177147 * m + 18554 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 27455
  rw [data_18_27455.1, data_18_27455.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_27455 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 27455) < 262144 * m + 27455 := by
  apply descent_of_endpoint
  · rw [data_18_27455.1]; exact data_18_27455.2.2
  · rw [data_18_27455.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 27463). -/
theorem data_18_27463 : oddCount 27463 18 = 11 ∧
    acceleratedOrbit 18 27463 = 18560 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_27463 : ∀ j : Fin 18,
    27463 ≤ acceleratedOrbit j.val 27463 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_27463 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 27463) = 177147 * m + 18560 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 27463
  rw [data_18_27463.1, data_18_27463.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_27463 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 27463) < 262144 * m + 27463 := by
  apply descent_of_endpoint
  · rw [data_18_27463.1]; exact data_18_27463.2.2
  · rw [data_18_27463.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 27495). -/
theorem data_18_27495 : oddCount 27495 18 = 11 ∧
    acceleratedOrbit 18 27495 = 18581 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_27495 : ∀ j : Fin 18,
    27495 ≤ acceleratedOrbit j.val 27495 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_27495 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 27495) = 177147 * m + 18581 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 27495
  rw [data_18_27495.1, data_18_27495.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_27495 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 27495) < 262144 * m + 27495 := by
  apply descent_of_endpoint
  · rw [data_18_27495.1]; exact data_18_27495.2.2
  · rw [data_18_27495.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 27503). -/
theorem data_18_27503 : oddCount 27503 18 = 11 ∧
    acceleratedOrbit 18 27503 = 18587 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_27503 : ∀ j : Fin 18,
    27503 ≤ acceleratedOrbit j.val 27503 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_27503 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 27503) = 177147 * m + 18587 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 27503
  rw [data_18_27503.1, data_18_27503.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_27503 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 27503) < 262144 * m + 27503 := by
  apply descent_of_endpoint
  · rw [data_18_27503.1]; exact data_18_27503.2.2
  · rw [data_18_27503.2.1]; decide

end Collatz.Research.FirstDescent.Batch112
