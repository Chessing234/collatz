import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 132. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch132
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 67303). -/
theorem data_18_67303 : oddCount 67303 18 = 11 ∧
    acceleratedOrbit 18 67303 = 45482 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_67303 : ∀ j : Fin 18,
    67303 ≤ acceleratedOrbit j.val 67303 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_67303 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 67303) = 177147 * m + 45482 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 67303
  rw [data_18_67303.1, data_18_67303.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_67303 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 67303) < 262144 * m + 67303 := by
  apply descent_of_endpoint
  · rw [data_18_67303.1]; exact data_18_67303.2.2
  · rw [data_18_67303.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 67791). -/
theorem data_18_67791 : oddCount 67791 18 = 11 ∧
    acceleratedOrbit 18 67791 = 45812 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_67791 : ∀ j : Fin 18,
    67791 ≤ acceleratedOrbit j.val 67791 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_67791 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 67791) = 177147 * m + 45812 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 67791
  rw [data_18_67791.1, data_18_67791.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_67791 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 67791) < 262144 * m + 67791 := by
  apply descent_of_endpoint
  · rw [data_18_67791.1]; exact data_18_67791.2.2
  · rw [data_18_67791.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 68351). -/
theorem data_18_68351 : oddCount 68351 18 = 11 ∧
    acceleratedOrbit 18 68351 = 46190 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_68351 : ∀ j : Fin 18,
    68351 ≤ acceleratedOrbit j.val 68351 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_68351 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 68351) = 177147 * m + 46190 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 68351
  rw [data_18_68351.1, data_18_68351.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_68351 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 68351) < 262144 * m + 68351 := by
  apply descent_of_endpoint
  · rw [data_18_68351.1]; exact data_18_68351.2.2
  · rw [data_18_68351.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 68635). -/
theorem data_18_68635 : oddCount 68635 18 = 11 ∧
    acceleratedOrbit 18 68635 = 46382 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_68635 : ∀ j : Fin 18,
    68635 ≤ acceleratedOrbit j.val 68635 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_68635 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 68635) = 177147 * m + 46382 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 68635
  rw [data_18_68635.1, data_18_68635.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_68635 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 68635) < 262144 * m + 68635 := by
  apply descent_of_endpoint
  · rw [data_18_68635.1]; exact data_18_68635.2.2
  · rw [data_18_68635.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 68815). -/
theorem data_18_68815 : oddCount 68815 18 = 11 ∧
    acceleratedOrbit 18 68815 = 46504 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_68815 : ∀ j : Fin 18,
    68815 ≤ acceleratedOrbit j.val 68815 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_68815 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 68815) = 177147 * m + 46504 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 68815
  rw [data_18_68815.1, data_18_68815.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_68815 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 68815) < 262144 * m + 68815 := by
  apply descent_of_endpoint
  · rw [data_18_68815.1]; exact data_18_68815.2.2
  · rw [data_18_68815.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 68847). -/
theorem data_18_68847 : oddCount 68847 18 = 11 ∧
    acceleratedOrbit 18 68847 = 46525 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_68847 : ∀ j : Fin 18,
    68847 ≤ acceleratedOrbit j.val 68847 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_68847 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 68847) = 177147 * m + 46525 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 68847
  rw [data_18_68847.1, data_18_68847.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_68847 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 68847) < 262144 * m + 68847 := by
  apply descent_of_endpoint
  · rw [data_18_68847.1]; exact data_18_68847.2.2
  · rw [data_18_68847.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 68891). -/
theorem data_18_68891 : oddCount 68891 18 = 11 ∧
    acceleratedOrbit 18 68891 = 46555 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_68891 : ∀ j : Fin 18,
    68891 ≤ acceleratedOrbit j.val 68891 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_68891 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 68891) = 177147 * m + 46555 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 68891
  rw [data_18_68891.1, data_18_68891.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_68891 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 68891) < 262144 * m + 68891 := by
  apply descent_of_endpoint
  · rw [data_18_68891.1]; exact data_18_68891.2.2
  · rw [data_18_68891.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 68935). -/
theorem data_18_68935 : oddCount 68935 18 = 11 ∧
    acceleratedOrbit 18 68935 = 46585 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_68935 : ∀ j : Fin 18,
    68935 ≤ acceleratedOrbit j.val 68935 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_68935 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 68935) = 177147 * m + 46585 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 68935
  rw [data_18_68935.1, data_18_68935.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_68935 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 68935) < 262144 * m + 68935 := by
  apply descent_of_endpoint
  · rw [data_18_68935.1]; exact data_18_68935.2.2
  · rw [data_18_68935.2.1]; decide

end Collatz.Research.FirstDescent.Batch132
