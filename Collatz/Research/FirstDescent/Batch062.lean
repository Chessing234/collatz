import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 62. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch062
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 24731). -/
theorem data_16_24731 : oddCount 24731 16 = 10 ∧
    acceleratedOrbit 16 24731 = 22285 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_24731 : ∀ j : Fin 16,
    24731 ≤ acceleratedOrbit j.val 24731 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_24731 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 24731) = 59049 * m + 22285 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 24731
  rw [data_16_24731.1, data_16_24731.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_24731 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 24731) < 65536 * m + 24731 := by
  apply descent_of_endpoint
  · rw [data_16_24731.1]; exact data_16_24731.2.2
  · rw [data_16_24731.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 24815). -/
theorem data_16_24815 : oddCount 24815 16 = 10 ∧
    acceleratedOrbit 16 24815 = 22360 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_24815 : ∀ j : Fin 16,
    24815 ≤ acceleratedOrbit j.val 24815 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_24815 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 24815) = 59049 * m + 22360 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 24815
  rw [data_16_24815.1, data_16_24815.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_24815 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 24815) < 65536 * m + 24815 := by
  apply descent_of_endpoint
  · rw [data_16_24815.1]; exact data_16_24815.2.2
  · rw [data_16_24815.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 25371). -/
theorem data_16_25371 : oddCount 25371 16 = 10 ∧
    acceleratedOrbit 16 25371 = 22861 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_25371 : ∀ j : Fin 16,
    25371 ≤ acceleratedOrbit j.val 25371 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_25371 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 25371) = 59049 * m + 22861 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 25371
  rw [data_16_25371.1, data_16_25371.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_25371 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 25371) < 65536 * m + 25371 := by
  apply descent_of_endpoint
  · rw [data_16_25371.1]; exact data_16_25371.2.2
  · rw [data_16_25371.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 25415). -/
theorem data_16_25415 : oddCount 25415 16 = 10 ∧
    acceleratedOrbit 16 25415 = 22901 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_25415 : ∀ j : Fin 16,
    25415 ≤ acceleratedOrbit j.val 25415 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_25415 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 25415) = 59049 * m + 22901 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 25415
  rw [data_16_25415.1, data_16_25415.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_25415 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 25415) < 65536 * m + 25415 := by
  apply descent_of_endpoint
  · rw [data_16_25415.1]; exact data_16_25415.2.2
  · rw [data_16_25415.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 25471). -/
theorem data_16_25471 : oddCount 25471 16 = 10 ∧
    acceleratedOrbit 16 25471 = 22951 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_25471 : ∀ j : Fin 16,
    25471 ≤ acceleratedOrbit j.val 25471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_25471 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 25471) = 59049 * m + 22951 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 25471
  rw [data_16_25471.1, data_16_25471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_25471 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 25471) < 65536 * m + 25471 := by
  apply descent_of_endpoint
  · rw [data_16_25471.1]; exact data_16_25471.2.2
  · rw [data_16_25471.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 25599). -/
theorem data_16_25599 : oddCount 25599 16 = 10 ∧
    acceleratedOrbit 16 25599 = 23066 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_25599 : ∀ j : Fin 16,
    25599 ≤ acceleratedOrbit j.val 25599 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_25599 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 25599) = 59049 * m + 23066 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 25599
  rw [data_16_25599.1, data_16_25599.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_25599 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 25599) < 65536 * m + 25599 := by
  apply descent_of_endpoint
  · rw [data_16_25599.1]; exact data_16_25599.2.2
  · rw [data_16_25599.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 25671). -/
theorem data_16_25671 : oddCount 25671 16 = 10 ∧
    acceleratedOrbit 16 25671 = 23132 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_25671 : ∀ j : Fin 16,
    25671 ≤ acceleratedOrbit j.val 25671 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_25671 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 25671) = 59049 * m + 23132 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 25671
  rw [data_16_25671.1, data_16_25671.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_25671 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 25671) < 65536 * m + 25671 := by
  apply descent_of_endpoint
  · rw [data_16_25671.1]; exact data_16_25671.2.2
  · rw [data_16_25671.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 25851). -/
theorem data_16_25851 : oddCount 25851 16 = 10 ∧
    acceleratedOrbit 16 25851 = 23294 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_25851 : ∀ j : Fin 16,
    25851 ≤ acceleratedOrbit j.val 25851 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_25851 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 25851) = 59049 * m + 23294 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 25851
  rw [data_16_25851.1, data_16_25851.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_25851 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 25851) < 65536 * m + 25851 := by
  apply descent_of_endpoint
  · rw [data_16_25851.1]; exact data_16_25851.2.2
  · rw [data_16_25851.2.1]; decide

end Collatz.Research.FirstDescent.Batch062
