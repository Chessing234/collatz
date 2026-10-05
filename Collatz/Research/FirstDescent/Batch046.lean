import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 46. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch046
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 6703). -/
theorem data_16_6703 : oddCount 6703 16 = 10 ∧
    acceleratedOrbit 16 6703 = 6041 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_6703 : ∀ j : Fin 16,
    6703 ≤ acceleratedOrbit j.val 6703 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_6703 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 6703) = 59049 * m + 6041 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 6703
  rw [data_16_6703.1, data_16_6703.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_6703 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 6703) < 65536 * m + 6703 := by
  apply descent_of_endpoint
  · rw [data_16_6703.1]; exact data_16_6703.2.2
  · rw [data_16_6703.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 6975). -/
theorem data_16_6975 : oddCount 6975 16 = 10 ∧
    acceleratedOrbit 16 6975 = 6286 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_6975 : ∀ j : Fin 16,
    6975 ≤ acceleratedOrbit j.val 6975 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_6975 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 6975) = 59049 * m + 6286 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 6975
  rw [data_16_6975.1, data_16_6975.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_6975 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 6975) < 65536 * m + 6975 := by
  apply descent_of_endpoint
  · rw [data_16_6975.1]; exact data_16_6975.2.2
  · rw [data_16_6975.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 7015). -/
theorem data_16_7015 : oddCount 7015 16 = 10 ∧
    acceleratedOrbit 16 7015 = 6322 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_7015 : ∀ j : Fin 16,
    7015 ≤ acceleratedOrbit j.val 7015 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_7015 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 7015) = 59049 * m + 6322 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 7015
  rw [data_16_7015.1, data_16_7015.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_7015 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 7015) < 65536 * m + 7015 := by
  apply descent_of_endpoint
  · rw [data_16_7015.1]; exact data_16_7015.2.2
  · rw [data_16_7015.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 7103). -/
theorem data_16_7103 : oddCount 7103 16 = 10 ∧
    acceleratedOrbit 16 7103 = 6401 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_7103 : ∀ j : Fin 16,
    7103 ≤ acceleratedOrbit j.val 7103 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_7103 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 7103) = 59049 * m + 6401 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 7103
  rw [data_16_7103.1, data_16_7103.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_7103 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 7103) < 65536 * m + 7103 := by
  apply descent_of_endpoint
  · rw [data_16_7103.1]; exact data_16_7103.2.2
  · rw [data_16_7103.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 7231). -/
theorem data_16_7231 : oddCount 7231 16 = 10 ∧
    acceleratedOrbit 16 7231 = 6517 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_7231 : ∀ j : Fin 16,
    7231 ≤ acceleratedOrbit j.val 7231 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_7231 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 7231) = 59049 * m + 6517 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 7231
  rw [data_16_7231.1, data_16_7231.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_7231 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 7231) < 65536 * m + 7231 := by
  apply descent_of_endpoint
  · rw [data_16_7231.1]; exact data_16_7231.2.2
  · rw [data_16_7231.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 7451). -/
theorem data_16_7451 : oddCount 7451 16 = 10 ∧
    acceleratedOrbit 16 7451 = 6715 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_7451 : ∀ j : Fin 16,
    7451 ≤ acceleratedOrbit j.val 7451 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_7451 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 7451) = 59049 * m + 6715 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 7451
  rw [data_16_7451.1, data_16_7451.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_7451 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 7451) < 65536 * m + 7451 := by
  apply descent_of_endpoint
  · rw [data_16_7451.1]; exact data_16_7451.2.2
  · rw [data_16_7451.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 7471). -/
theorem data_16_7471 : oddCount 7471 16 = 10 ∧
    acceleratedOrbit 16 7471 = 6733 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_7471 : ∀ j : Fin 16,
    7471 ≤ acceleratedOrbit j.val 7471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_7471 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 7471) = 59049 * m + 6733 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 7471
  rw [data_16_7471.1, data_16_7471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_7471 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 7471) < 65536 * m + 7471 := by
  apply descent_of_endpoint
  · rw [data_16_7471.1]; exact data_16_7471.2.2
  · rw [data_16_7471.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 7551). -/
theorem data_16_7551 : oddCount 7551 16 = 10 ∧
    acceleratedOrbit 16 7551 = 6805 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_7551 : ∀ j : Fin 16,
    7551 ≤ acceleratedOrbit j.val 7551 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_7551 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 7551) = 59049 * m + 6805 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 7551
  rw [data_16_7551.1, data_16_7551.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_7551 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 7551) < 65536 * m + 7551 := by
  apply descent_of_endpoint
  · rw [data_16_7551.1]; exact data_16_7551.2.2
  · rw [data_16_7551.2.1]; decide

end Collatz.Research.FirstDescent.Batch046
