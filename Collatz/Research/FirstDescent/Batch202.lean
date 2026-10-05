import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 202. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch202
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 221511). -/
theorem data_18_221511 : oddCount 221511 18 = 11 ∧
    acceleratedOrbit 18 221511 = 149690 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_221511 : ∀ j : Fin 18,
    221511 ≤ acceleratedOrbit j.val 221511 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_221511 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 221511) = 177147 * m + 149690 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 221511
  rw [data_18_221511.1, data_18_221511.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_221511 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 221511) < 262144 * m + 221511 := by
  apply descent_of_endpoint
  · rw [data_18_221511.1]; exact data_18_221511.2.2
  · rw [data_18_221511.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 221595). -/
theorem data_18_221595 : oddCount 221595 18 = 11 ∧
    acceleratedOrbit 18 221595 = 149747 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_221595 : ∀ j : Fin 18,
    221595 ≤ acceleratedOrbit j.val 221595 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_221595 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 221595) = 177147 * m + 149747 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 221595
  rw [data_18_221595.1, data_18_221595.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_221595 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 221595) < 262144 * m + 221595 := by
  apply descent_of_endpoint
  · rw [data_18_221595.1]; exact data_18_221595.2.2
  · rw [data_18_221595.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 222043). -/
theorem data_18_222043 : oddCount 222043 18 = 11 ∧
    acceleratedOrbit 18 222043 = 150050 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_222043 : ∀ j : Fin 18,
    222043 ≤ acceleratedOrbit j.val 222043 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_222043 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 222043) = 177147 * m + 150050 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 222043
  rw [data_18_222043.1, data_18_222043.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_222043 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 222043) < 262144 * m + 222043 := by
  apply descent_of_endpoint
  · rw [data_18_222043.1]; exact data_18_222043.2.2
  · rw [data_18_222043.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 222363). -/
theorem data_18_222363 : oddCount 222363 18 = 11 ∧
    acceleratedOrbit 18 222363 = 150266 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_222363 : ∀ j : Fin 18,
    222363 ≤ acceleratedOrbit j.val 222363 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_222363 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 222363) = 177147 * m + 150266 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 222363
  rw [data_18_222363.1, data_18_222363.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_222363 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 222363) < 262144 * m + 222363 := by
  apply descent_of_endpoint
  · rw [data_18_222363.1]; exact data_18_222363.2.2
  · rw [data_18_222363.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 222491). -/
theorem data_18_222491 : oddCount 222491 18 = 11 ∧
    acceleratedOrbit 18 222491 = 150352 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_222491 : ∀ j : Fin 18,
    222491 ≤ acceleratedOrbit j.val 222491 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_222491 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 222491) = 177147 * m + 150352 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 222491
  rw [data_18_222491.1, data_18_222491.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_222491 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 222491) < 262144 * m + 222491 := by
  apply descent_of_endpoint
  · rw [data_18_222491.1]; exact data_18_222491.2.2
  · rw [data_18_222491.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 222535). -/
theorem data_18_222535 : oddCount 222535 18 = 11 ∧
    acceleratedOrbit 18 222535 = 150382 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_222535 : ∀ j : Fin 18,
    222535 ≤ acceleratedOrbit j.val 222535 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_222535 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 222535) = 177147 * m + 150382 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 222535
  rw [data_18_222535.1, data_18_222535.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_222535 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 222535) < 262144 * m + 222535 := by
  apply descent_of_endpoint
  · rw [data_18_222535.1]; exact data_18_222535.2.2
  · rw [data_18_222535.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 222879). -/
theorem data_18_222879 : oddCount 222879 18 = 11 ∧
    acceleratedOrbit 18 222879 = 150614 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_222879 : ∀ j : Fin 18,
    222879 ≤ acceleratedOrbit j.val 222879 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_222879 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 222879) = 177147 * m + 150614 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 222879
  rw [data_18_222879.1, data_18_222879.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_222879 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 222879) < 262144 * m + 222879 := by
  apply descent_of_endpoint
  · rw [data_18_222879.1]; exact data_18_222879.2.2
  · rw [data_18_222879.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 223087). -/
theorem data_18_223087 : oddCount 223087 18 = 11 ∧
    acceleratedOrbit 18 223087 = 150755 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_223087 : ∀ j : Fin 18,
    223087 ≤ acceleratedOrbit j.val 223087 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_223087 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 223087) = 177147 * m + 150755 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 223087
  rw [data_18_223087.1, data_18_223087.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_223087 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 223087) < 262144 * m + 223087 := by
  apply descent_of_endpoint
  · rw [data_18_223087.1]; exact data_18_223087.2.2
  · rw [data_18_223087.2.1]; decide

end Collatz.Research.FirstDescent.Batch202
