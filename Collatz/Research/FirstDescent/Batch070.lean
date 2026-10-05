import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 70. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch070
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 33007). -/
theorem data_16_33007 : oddCount 33007 16 = 10 ∧
    acceleratedOrbit 16 33007 = 29741 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_33007 : ∀ j : Fin 16,
    33007 ≤ acceleratedOrbit j.val 33007 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_33007 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 33007) = 59049 * m + 29741 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 33007
  rw [data_16_33007.1, data_16_33007.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_33007 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 33007) < 65536 * m + 33007 := by
  apply descent_of_endpoint
  · rw [data_16_33007.1]; exact data_16_33007.2.2
  · rw [data_16_33007.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 33087). -/
theorem data_16_33087 : oddCount 33087 16 = 10 ∧
    acceleratedOrbit 16 33087 = 29813 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_33087 : ∀ j : Fin 16,
    33087 ≤ acceleratedOrbit j.val 33087 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_33087 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 33087) = 59049 * m + 29813 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 33087
  rw [data_16_33087.1, data_16_33087.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_33087 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 33087) < 65536 * m + 33087 := by
  apply descent_of_endpoint
  · rw [data_16_33087.1]; exact data_16_33087.2.2
  · rw [data_16_33087.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 33255). -/
theorem data_16_33255 : oddCount 33255 16 = 10 ∧
    acceleratedOrbit 16 33255 = 29965 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_33255 : ∀ j : Fin 16,
    33255 ≤ acceleratedOrbit j.val 33255 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_33255 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 33255) = 59049 * m + 29965 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 33255
  rw [data_16_33255.1, data_16_33255.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_33255 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 33255) < 65536 * m + 33255 := by
  apply descent_of_endpoint
  · rw [data_16_33255.1]; exact data_16_33255.2.2
  · rw [data_16_33255.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 33531). -/
theorem data_16_33531 : oddCount 33531 16 = 10 ∧
    acceleratedOrbit 16 33531 = 30214 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_33531 : ∀ j : Fin 16,
    33531 ≤ acceleratedOrbit j.val 33531 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_33531 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 33531) = 59049 * m + 30214 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 33531
  rw [data_16_33531.1, data_16_33531.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_33531 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 33531) < 65536 * m + 33531 := by
  apply descent_of_endpoint
  · rw [data_16_33531.1]; exact data_16_33531.2.2
  · rw [data_16_33531.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 33663). -/
theorem data_16_33663 : oddCount 33663 16 = 10 ∧
    acceleratedOrbit 16 33663 = 30332 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_33663 : ∀ j : Fin 16,
    33663 ≤ acceleratedOrbit j.val 33663 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_33663 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 33663) = 59049 * m + 30332 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 33663
  rw [data_16_33663.1, data_16_33663.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_33663 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 33663) < 65536 * m + 33663 := by
  apply descent_of_endpoint
  · rw [data_16_33663.1]; exact data_16_33663.2.2
  · rw [data_16_33663.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 34111). -/
theorem data_16_34111 : oddCount 34111 16 = 10 ∧
    acceleratedOrbit 16 34111 = 30736 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_34111 : ∀ j : Fin 16,
    34111 ≤ acceleratedOrbit j.val 34111 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_34111 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 34111) = 59049 * m + 30736 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 34111
  rw [data_16_34111.1, data_16_34111.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_34111 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 34111) < 65536 * m + 34111 := by
  apply descent_of_endpoint
  · rw [data_16_34111.1]; exact data_16_34111.2.2
  · rw [data_16_34111.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 34151). -/
theorem data_16_34151 : oddCount 34151 16 = 10 ∧
    acceleratedOrbit 16 34151 = 30772 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_34151 : ∀ j : Fin 16,
    34151 ≤ acceleratedOrbit j.val 34151 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_34151 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 34151) = 59049 * m + 30772 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 34151
  rw [data_16_34151.1, data_16_34151.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_34151 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 34151) < 65536 * m + 34151 := by
  apply descent_of_endpoint
  · rw [data_16_34151.1]; exact data_16_34151.2.2
  · rw [data_16_34151.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 34255). -/
theorem data_16_34255 : oddCount 34255 16 = 10 ∧
    acceleratedOrbit 16 34255 = 30866 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_34255 : ∀ j : Fin 16,
    34255 ≤ acceleratedOrbit j.val 34255 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_34255 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 34255) = 59049 * m + 30866 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 34255
  rw [data_16_34255.1, data_16_34255.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_34255 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 34255) < 65536 * m + 34255 := by
  apply descent_of_endpoint
  · rw [data_16_34255.1]; exact data_16_34255.2.2
  · rw [data_16_34255.2.1]; decide

end Collatz.Research.FirstDescent.Batch070
