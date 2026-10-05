import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 162. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch162
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 130587). -/
theorem data_18_130587 : oddCount 130587 18 = 11 ∧
    acceleratedOrbit 18 130587 = 88247 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_130587 : ∀ j : Fin 18,
    130587 ≤ acceleratedOrbit j.val 130587 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_130587 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 130587) = 177147 * m + 88247 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 130587
  rw [data_18_130587.1, data_18_130587.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_130587 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 130587) < 262144 * m + 130587 := by
  apply descent_of_endpoint
  · rw [data_18_130587.1]; exact data_18_130587.2.2
  · rw [data_18_130587.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 130799). -/
theorem data_18_130799 : oddCount 130799 18 = 11 ∧
    acceleratedOrbit 18 130799 = 88390 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_130799 : ∀ j : Fin 18,
    130799 ≤ acceleratedOrbit j.val 130799 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_130799 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 130799) = 177147 * m + 88390 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 130799
  rw [data_18_130799.1, data_18_130799.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_130799 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 130799) < 262144 * m + 130799 := by
  apply descent_of_endpoint
  · rw [data_18_130799.1]; exact data_18_130799.2.2
  · rw [data_18_130799.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 131311). -/
theorem data_18_131311 : oddCount 131311 18 = 11 ∧
    acceleratedOrbit 18 131311 = 88736 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_131311 : ∀ j : Fin 18,
    131311 ≤ acceleratedOrbit j.val 131311 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_131311 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 131311) = 177147 * m + 88736 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 131311
  rw [data_18_131311.1, data_18_131311.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_131311 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 131311) < 262144 * m + 131311 := by
  apply descent_of_endpoint
  · rw [data_18_131311.1]; exact data_18_131311.2.2
  · rw [data_18_131311.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 131391). -/
theorem data_18_131391 : oddCount 131391 18 = 11 ∧
    acceleratedOrbit 18 131391 = 88790 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_131391 : ∀ j : Fin 18,
    131391 ≤ acceleratedOrbit j.val 131391 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_131391 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 131391) = 177147 * m + 88790 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 131391
  rw [data_18_131391.1, data_18_131391.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_131391 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 131391) < 262144 * m + 131391 := by
  apply descent_of_endpoint
  · rw [data_18_131391.1]; exact data_18_131391.2.2
  · rw [data_18_131391.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 131559). -/
theorem data_18_131559 : oddCount 131559 18 = 11 ∧
    acceleratedOrbit 18 131559 = 88904 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_131559 : ∀ j : Fin 18,
    131559 ≤ acceleratedOrbit j.val 131559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_131559 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 131559) = 177147 * m + 88904 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 131559
  rw [data_18_131559.1, data_18_131559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_131559 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 131559) < 262144 * m + 131559 := by
  apply descent_of_endpoint
  · rw [data_18_131559.1]; exact data_18_131559.2.2
  · rw [data_18_131559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 132583). -/
theorem data_18_132583 : oddCount 132583 18 = 11 ∧
    acceleratedOrbit 18 132583 = 89596 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_132583 : ∀ j : Fin 18,
    132583 ≤ acceleratedOrbit j.val 132583 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_132583 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 132583) = 177147 * m + 89596 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 132583
  rw [data_18_132583.1, data_18_132583.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_132583 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 132583) < 262144 * m + 132583 := by
  apply descent_of_endpoint
  · rw [data_18_132583.1]; exact data_18_132583.2.2
  · rw [data_18_132583.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 132735). -/
theorem data_18_132735 : oddCount 132735 18 = 11 ∧
    acceleratedOrbit 18 132735 = 89698 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_132735 : ∀ j : Fin 18,
    132735 ≤ acceleratedOrbit j.val 132735 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_132735 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 132735) = 177147 * m + 89698 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 132735
  rw [data_18_132735.1, data_18_132735.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_132735 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 132735) < 262144 * m + 132735 := by
  apply descent_of_endpoint
  · rw [data_18_132735.1]; exact data_18_132735.2.2
  · rw [data_18_132735.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 132935). -/
theorem data_18_132935 : oddCount 132935 18 = 11 ∧
    acceleratedOrbit 18 132935 = 89834 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_132935 : ∀ j : Fin 18,
    132935 ≤ acceleratedOrbit j.val 132935 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_132935 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 132935) = 177147 * m + 89834 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 132935
  rw [data_18_132935.1, data_18_132935.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_132935 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 132935) < 262144 * m + 132935 := by
  apply descent_of_endpoint
  · rw [data_18_132935.1]; exact data_18_132935.2.2
  · rw [data_18_132935.2.1]; decide

end Collatz.Research.FirstDescent.Batch162
