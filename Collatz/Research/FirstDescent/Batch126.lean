import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 126. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch126
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 56351). -/
theorem data_18_56351 : oddCount 56351 18 = 11 ∧
    acceleratedOrbit 18 56351 = 38081 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_56351 : ∀ j : Fin 18,
    56351 ≤ acceleratedOrbit j.val 56351 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_56351 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 56351) = 177147 * m + 38081 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 56351
  rw [data_18_56351.1, data_18_56351.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_56351 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 56351) < 262144 * m + 56351 := by
  apply descent_of_endpoint
  · rw [data_18_56351.1]; exact data_18_56351.2.2
  · rw [data_18_56351.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 56431). -/
theorem data_18_56431 : oddCount 56431 18 = 11 ∧
    acceleratedOrbit 18 56431 = 38135 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_56431 : ∀ j : Fin 18,
    56431 ≤ acceleratedOrbit j.val 56431 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_56431 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 56431) = 177147 * m + 38135 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 56431
  rw [data_18_56431.1, data_18_56431.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_56431 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 56431) < 262144 * m + 56431 := by
  apply descent_of_endpoint
  · rw [data_18_56431.1]; exact data_18_56431.2.2
  · rw [data_18_56431.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 56475). -/
theorem data_18_56475 : oddCount 56475 18 = 11 ∧
    acceleratedOrbit 18 56475 = 38165 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_56475 : ∀ j : Fin 18,
    56475 ≤ acceleratedOrbit j.val 56475 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_56475 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 56475) = 177147 * m + 38165 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 56475
  rw [data_18_56475.1, data_18_56475.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_56475 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 56475) < 262144 * m + 56475 := by
  apply descent_of_endpoint
  · rw [data_18_56475.1]; exact data_18_56475.2.2
  · rw [data_18_56475.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 56511). -/
theorem data_18_56511 : oddCount 56511 18 = 11 ∧
    acceleratedOrbit 18 56511 = 38189 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_56511 : ∀ j : Fin 18,
    56511 ≤ acceleratedOrbit j.val 56511 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_56511 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 56511) = 177147 * m + 38189 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 56511
  rw [data_18_56511.1, data_18_56511.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_56511 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 56511) < 262144 * m + 56511 := by
  apply descent_of_endpoint
  · rw [data_18_56511.1]; exact data_18_56511.2.2
  · rw [data_18_56511.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 58087). -/
theorem data_18_58087 : oddCount 58087 18 = 11 ∧
    acceleratedOrbit 18 58087 = 39254 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_58087 : ∀ j : Fin 18,
    58087 ≤ acceleratedOrbit j.val 58087 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_58087 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 58087) = 177147 * m + 39254 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 58087
  rw [data_18_58087.1, data_18_58087.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_58087 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 58087) < 262144 * m + 58087 := by
  apply descent_of_endpoint
  · rw [data_18_58087.1]; exact data_18_58087.2.2
  · rw [data_18_58087.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 58107). -/
theorem data_18_58107 : oddCount 58107 18 = 11 ∧
    acceleratedOrbit 18 58107 = 39268 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_58107 : ∀ j : Fin 18,
    58107 ≤ acceleratedOrbit j.val 58107 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_58107 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 58107) = 177147 * m + 39268 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 58107
  rw [data_18_58107.1, data_18_58107.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_58107 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 58107) < 262144 * m + 58107 := by
  apply descent_of_endpoint
  · rw [data_18_58107.1]; exact data_18_58107.2.2
  · rw [data_18_58107.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 58367). -/
theorem data_18_58367 : oddCount 58367 18 = 11 ∧
    acceleratedOrbit 18 58367 = 39443 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_58367 : ∀ j : Fin 18,
    58367 ≤ acceleratedOrbit j.val 58367 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_58367 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 58367) = 177147 * m + 39443 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 58367
  rw [data_18_58367.1, data_18_58367.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_58367 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 58367) < 262144 * m + 58367 := by
  apply descent_of_endpoint
  · rw [data_18_58367.1]; exact data_18_58367.2.2
  · rw [data_18_58367.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 58619). -/
theorem data_18_58619 : oddCount 58619 18 = 11 ∧
    acceleratedOrbit 18 58619 = 39614 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_58619 : ∀ j : Fin 18,
    58619 ≤ acceleratedOrbit j.val 58619 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_58619 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 58619) = 177147 * m + 39614 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 58619
  rw [data_18_58619.1, data_18_58619.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_58619 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 58619) < 262144 * m + 58619 := by
  apply descent_of_endpoint
  · rw [data_18_58619.1]; exact data_18_58619.2.2
  · rw [data_18_58619.2.1]; decide

end Collatz.Research.FirstDescent.Batch126
