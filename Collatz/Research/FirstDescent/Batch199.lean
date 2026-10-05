import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 199. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch199
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 215451). -/
theorem data_18_215451 : oddCount 215451 18 = 11 ∧
    acceleratedOrbit 18 215451 = 145595 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_215451 : ∀ j : Fin 18,
    215451 ≤ acceleratedOrbit j.val 215451 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_215451 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 215451) = 177147 * m + 145595 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 215451
  rw [data_18_215451.1, data_18_215451.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_215451 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 215451) < 262144 * m + 215451 := by
  apply descent_of_endpoint
  · rw [data_18_215451.1]; exact data_18_215451.2.2
  · rw [data_18_215451.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 215663). -/
theorem data_18_215663 : oddCount 215663 18 = 11 ∧
    acceleratedOrbit 18 215663 = 145738 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_215663 : ∀ j : Fin 18,
    215663 ≤ acceleratedOrbit j.val 215663 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_215663 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 215663) = 177147 * m + 145738 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 215663
  rw [data_18_215663.1, data_18_215663.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_215663 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 215663) < 262144 * m + 215663 := by
  apply descent_of_endpoint
  · rw [data_18_215663.1]; exact data_18_215663.2.2
  · rw [data_18_215663.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 215783). -/
theorem data_18_215783 : oddCount 215783 18 = 11 ∧
    acceleratedOrbit 18 215783 = 145819 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_215783 : ∀ j : Fin 18,
    215783 ≤ acceleratedOrbit j.val 215783 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_215783 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 215783) = 177147 * m + 145819 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 215783
  rw [data_18_215783.1, data_18_215783.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_215783 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 215783) < 262144 * m + 215783 := by
  apply descent_of_endpoint
  · rw [data_18_215783.1]; exact data_18_215783.2.2
  · rw [data_18_215783.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 216175). -/
theorem data_18_216175 : oddCount 216175 18 = 11 ∧
    acceleratedOrbit 18 216175 = 146084 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_216175 : ∀ j : Fin 18,
    216175 ≤ acceleratedOrbit j.val 216175 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_216175 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 216175) = 177147 * m + 146084 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 216175
  rw [data_18_216175.1, data_18_216175.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_216175 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 216175) < 262144 * m + 216175 := by
  apply descent_of_endpoint
  · rw [data_18_216175.1]; exact data_18_216175.2.2
  · rw [data_18_216175.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 216255). -/
theorem data_18_216255 : oddCount 216255 18 = 11 ∧
    acceleratedOrbit 18 216255 = 146138 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_216255 : ∀ j : Fin 18,
    216255 ≤ acceleratedOrbit j.val 216255 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_216255 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 216255) = 177147 * m + 146138 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 216255
  rw [data_18_216255.1, data_18_216255.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_216255 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 216255) < 262144 * m + 216255 := by
  apply descent_of_endpoint
  · rw [data_18_216255.1]; exact data_18_216255.2.2
  · rw [data_18_216255.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 216575). -/
theorem data_18_216575 : oddCount 216575 18 = 11 ∧
    acceleratedOrbit 18 216575 = 146354 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_216575 : ∀ j : Fin 18,
    216575 ≤ acceleratedOrbit j.val 216575 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_216575 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 216575) = 177147 * m + 146354 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 216575
  rw [data_18_216575.1, data_18_216575.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_216575 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 216575) < 262144 * m + 216575 := by
  apply descent_of_endpoint
  · rw [data_18_216575.1]; exact data_18_216575.2.2
  · rw [data_18_216575.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 217023). -/
theorem data_18_217023 : oddCount 217023 18 = 11 ∧
    acceleratedOrbit 18 217023 = 146657 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_217023 : ∀ j : Fin 18,
    217023 ≤ acceleratedOrbit j.val 217023 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_217023 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 217023) = 177147 * m + 146657 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 217023
  rw [data_18_217023.1, data_18_217023.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_217023 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 217023) < 262144 * m + 217023 := by
  apply descent_of_endpoint
  · rw [data_18_217023.1]; exact data_18_217023.2.2
  · rw [data_18_217023.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 217767). -/
theorem data_18_217767 : oddCount 217767 18 = 11 ∧
    acceleratedOrbit 18 217767 = 147160 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_217767 : ∀ j : Fin 18,
    217767 ≤ acceleratedOrbit j.val 217767 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_217767 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 217767) = 177147 * m + 147160 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 217767
  rw [data_18_217767.1, data_18_217767.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_217767 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 217767) < 262144 * m + 217767 := by
  apply descent_of_endpoint
  · rw [data_18_217767.1]; exact data_18_217767.2.2
  · rw [data_18_217767.2.1]; decide

end Collatz.Research.FirstDescent.Batch199
