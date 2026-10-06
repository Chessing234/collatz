import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 64. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch064
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 27039). -/
theorem data_16_27039 : oddCount 27039 16 = 10 ∧
    acceleratedOrbit 16 27039 = 24364 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_27039 : ∀ j : Fin 16,
    27039 ≤ acceleratedOrbit j.val 27039 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_27039 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27039) = 59049 * m + 24364 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 27039
  rw [data_16_27039.1, data_16_27039.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_27039 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27039) < 65536 * m + 27039 := by
  apply descent_of_endpoint
  · rw [data_16_27039.1]; exact data_16_27039.2.2
  · rw [data_16_27039.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 27119). -/
theorem data_16_27119 : oddCount 27119 16 = 10 ∧
    acceleratedOrbit 16 27119 = 24436 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_27119 : ∀ j : Fin 16,
    27119 ≤ acceleratedOrbit j.val 27119 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_27119 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27119) = 59049 * m + 24436 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 27119
  rw [data_16_27119.1, data_16_27119.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_27119 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27119) < 65536 * m + 27119 := by
  apply descent_of_endpoint
  · rw [data_16_27119.1]; exact data_16_27119.2.2
  · rw [data_16_27119.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 27303). -/
theorem data_16_27303 : oddCount 27303 16 = 10 ∧
    acceleratedOrbit 16 27303 = 24602 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_27303 : ∀ j : Fin 16,
    27303 ≤ acceleratedOrbit j.val 27303 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_27303 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27303) = 59049 * m + 24602 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 27303
  rw [data_16_27303.1, data_16_27303.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_27303 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27303) < 65536 * m + 27303 := by
  apply descent_of_endpoint
  · rw [data_16_27303.1]; exact data_16_27303.2.2
  · rw [data_16_27303.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 27343). -/
theorem data_16_27343 : oddCount 27343 16 = 10 ∧
    acceleratedOrbit 16 27343 = 24638 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_27343 : ∀ j : Fin 16,
    27343 ≤ acceleratedOrbit j.val 27343 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_27343 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27343) = 59049 * m + 24638 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 27343
  rw [data_16_27343.1, data_16_27343.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_27343 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27343) < 65536 * m + 27343 := by
  apply descent_of_endpoint
  · rw [data_16_27343.1]; exact data_16_27343.2.2
  · rw [data_16_27343.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 27423). -/
theorem data_16_27423 : oddCount 27423 16 = 10 ∧
    acceleratedOrbit 16 27423 = 24710 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_27423 : ∀ j : Fin 16,
    27423 ≤ acceleratedOrbit j.val 27423 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_27423 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27423) = 59049 * m + 24710 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 27423
  rw [data_16_27423.1, data_16_27423.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_27423 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27423) < 65536 * m + 27423 := by
  apply descent_of_endpoint
  · rw [data_16_27423.1]; exact data_16_27423.2.2
  · rw [data_16_27423.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 27559). -/
theorem data_16_27559 : oddCount 27559 16 = 10 ∧
    acceleratedOrbit 16 27559 = 24833 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_27559 : ∀ j : Fin 16,
    27559 ≤ acceleratedOrbit j.val 27559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_27559 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27559) = 59049 * m + 24833 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 27559
  rw [data_16_27559.1, data_16_27559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_27559 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27559) < 65536 * m + 27559 := by
  apply descent_of_endpoint
  · rw [data_16_27559.1]; exact data_16_27559.2.2
  · rw [data_16_27559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 27675). -/
theorem data_16_27675 : oddCount 27675 16 = 10 ∧
    acceleratedOrbit 16 27675 = 24937 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_27675 : ∀ j : Fin 16,
    27675 ≤ acceleratedOrbit j.val 27675 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_27675 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27675) = 59049 * m + 24937 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 27675
  rw [data_16_27675.1, data_16_27675.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_27675 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27675) < 65536 * m + 27675 := by
  apply descent_of_endpoint
  · rw [data_16_27675.1]; exact data_16_27675.2.2
  · rw [data_16_27675.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 27739). -/
theorem data_16_27739 : oddCount 27739 16 = 10 ∧
    acceleratedOrbit 16 27739 = 24995 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_27739 : ∀ j : Fin 16,
    27739 ≤ acceleratedOrbit j.val 27739 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_27739 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27739) = 59049 * m + 24995 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 27739
  rw [data_16_27739.1, data_16_27739.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_27739 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27739) < 65536 * m + 27739 := by
  apply descent_of_endpoint
  · rw [data_16_27739.1]; exact data_16_27739.2.2
  · rw [data_16_27739.2.1]; decide

end Collatz.Research.FirstDescent.Batch064
