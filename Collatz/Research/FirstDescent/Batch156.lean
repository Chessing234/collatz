import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 156. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch156
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 117531). -/
theorem data_18_117531 : oddCount 117531 18 = 11 ∧
    acceleratedOrbit 18 117531 = 79424 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_117531 : ∀ j : Fin 18,
    117531 ≤ acceleratedOrbit j.val 117531 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_117531 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 117531) = 177147 * m + 79424 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 117531
  rw [data_18_117531.1, data_18_117531.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_117531 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 117531) < 262144 * m + 117531 := by
  apply descent_of_endpoint
  · rw [data_18_117531.1]; exact data_18_117531.2.2
  · rw [data_18_117531.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 117535). -/
theorem data_18_117535 : oddCount 117535 18 = 11 ∧
    acceleratedOrbit 18 117535 = 79427 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_117535 : ∀ j : Fin 18,
    117535 ≤ acceleratedOrbit j.val 117535 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_117535 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 117535) = 177147 * m + 79427 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 117535
  rw [data_18_117535.1, data_18_117535.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_117535 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 117535) < 262144 * m + 117535 := by
  apply descent_of_endpoint
  · rw [data_18_117535.1]; exact data_18_117535.2.2
  · rw [data_18_117535.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 118439). -/
theorem data_18_118439 : oddCount 118439 18 = 11 ∧
    acceleratedOrbit 18 118439 = 80038 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_118439 : ∀ j : Fin 18,
    118439 ≤ acceleratedOrbit j.val 118439 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_118439 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 118439) = 177147 * m + 80038 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 118439
  rw [data_18_118439.1, data_18_118439.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_118439 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 118439) < 262144 * m + 118439 := by
  apply descent_of_endpoint
  · rw [data_18_118439.1]; exact data_18_118439.2.2
  · rw [data_18_118439.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 118555). -/
theorem data_18_118555 : oddCount 118555 18 = 11 ∧
    acceleratedOrbit 18 118555 = 80116 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_118555 : ∀ j : Fin 18,
    118555 ≤ acceleratedOrbit j.val 118555 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_118555 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 118555) = 177147 * m + 80116 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 118555
  rw [data_18_118555.1, data_18_118555.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_118555 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 118555) < 262144 * m + 118555 := by
  apply descent_of_endpoint
  · rw [data_18_118555.1]; exact data_18_118555.2.2
  · rw [data_18_118555.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 118559). -/
theorem data_18_118559 : oddCount 118559 18 = 11 ∧
    acceleratedOrbit 18 118559 = 80119 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_118559 : ∀ j : Fin 18,
    118559 ≤ acceleratedOrbit j.val 118559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_118559 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 118559) = 177147 * m + 80119 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 118559
  rw [data_18_118559.1, data_18_118559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_118559 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 118559) < 262144 * m + 118559 := by
  apply descent_of_endpoint
  · rw [data_18_118559.1]; exact data_18_118559.2.2
  · rw [data_18_118559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 118639). -/
theorem data_18_118639 : oddCount 118639 18 = 11 ∧
    acceleratedOrbit 18 118639 = 80173 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_118639 : ∀ j : Fin 18,
    118639 ≤ acceleratedOrbit j.val 118639 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_118639 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 118639) = 177147 * m + 80173 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 118639
  rw [data_18_118639.1, data_18_118639.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_118639 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 118639) < 262144 * m + 118639 := by
  apply descent_of_endpoint
  · rw [data_18_118639.1]; exact data_18_118639.2.2
  · rw [data_18_118639.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 118991). -/
theorem data_18_118991 : oddCount 118991 18 = 11 ∧
    acceleratedOrbit 18 118991 = 80411 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_118991 : ∀ j : Fin 18,
    118991 ≤ acceleratedOrbit j.val 118991 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_118991 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 118991) = 177147 * m + 80411 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 118991
  rw [data_18_118991.1, data_18_118991.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_118991 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 118991) < 262144 * m + 118991 := by
  apply descent_of_endpoint
  · rw [data_18_118991.1]; exact data_18_118991.2.2
  · rw [data_18_118991.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 119039). -/
theorem data_18_119039 : oddCount 119039 18 = 11 ∧
    acceleratedOrbit 18 119039 = 80443 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_119039 : ∀ j : Fin 18,
    119039 ≤ acceleratedOrbit j.val 119039 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_119039 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 119039) = 177147 * m + 80443 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 119039
  rw [data_18_119039.1, data_18_119039.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_119039 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 119039) < 262144 * m + 119039 := by
  apply descent_of_endpoint
  · rw [data_18_119039.1]; exact data_18_119039.2.2
  · rw [data_18_119039.2.1]; decide

end Collatz.Research.FirstDescent.Batch156
