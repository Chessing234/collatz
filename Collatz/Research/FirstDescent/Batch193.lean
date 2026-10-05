import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 193. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch193
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 204635). -/
theorem data_18_204635 : oddCount 204635 18 = 11 ∧
    acceleratedOrbit 18 204635 = 138286 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_204635 : ∀ j : Fin 18,
    204635 ≤ acceleratedOrbit j.val 204635 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_204635 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 204635) = 177147 * m + 138286 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 204635
  rw [data_18_204635.1, data_18_204635.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_204635 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 204635) < 262144 * m + 204635 := by
  apply descent_of_endpoint
  · rw [data_18_204635.1]; exact data_18_204635.2.2
  · rw [data_18_204635.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 204735). -/
theorem data_18_204735 : oddCount 204735 18 = 11 ∧
    acceleratedOrbit 18 204735 = 138353 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_204735 : ∀ j : Fin 18,
    204735 ≤ acceleratedOrbit j.val 204735 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_204735 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 204735) = 177147 * m + 138353 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 204735
  rw [data_18_204735.1, data_18_204735.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_204735 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 204735) < 262144 * m + 204735 := by
  apply descent_of_endpoint
  · rw [data_18_204735.1]; exact data_18_204735.2.2
  · rw [data_18_204735.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 204783). -/
theorem data_18_204783 : oddCount 204783 18 = 11 ∧
    acceleratedOrbit 18 204783 = 138386 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_204783 : ∀ j : Fin 18,
    204783 ≤ acceleratedOrbit j.val 204783 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_204783 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 204783) = 177147 * m + 138386 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 204783
  rw [data_18_204783.1, data_18_204783.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_204783 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 204783) < 262144 * m + 204783 := by
  apply descent_of_endpoint
  · rw [data_18_204783.1]; exact data_18_204783.2.2
  · rw [data_18_204783.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 204831). -/
theorem data_18_204831 : oddCount 204831 18 = 11 ∧
    acceleratedOrbit 18 204831 = 138418 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_204831 : ∀ j : Fin 18,
    204831 ≤ acceleratedOrbit j.val 204831 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_204831 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 204831) = 177147 * m + 138418 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 204831
  rw [data_18_204831.1, data_18_204831.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_204831 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 204831) < 262144 * m + 204831 := by
  apply descent_of_endpoint
  · rw [data_18_204831.1]; exact data_18_204831.2.2
  · rw [data_18_204831.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 204863). -/
theorem data_18_204863 : oddCount 204863 18 = 11 ∧
    acceleratedOrbit 18 204863 = 138440 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_204863 : ∀ j : Fin 18,
    204863 ≤ acceleratedOrbit j.val 204863 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_204863 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 204863) = 177147 * m + 138440 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 204863
  rw [data_18_204863.1, data_18_204863.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_204863 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 204863) < 262144 * m + 204863 := by
  apply descent_of_endpoint
  · rw [data_18_204863.1]; exact data_18_204863.2.2
  · rw [data_18_204863.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 204903). -/
theorem data_18_204903 : oddCount 204903 18 = 11 ∧
    acceleratedOrbit 18 204903 = 138467 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_204903 : ∀ j : Fin 18,
    204903 ≤ acceleratedOrbit j.val 204903 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_204903 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 204903) = 177147 * m + 138467 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 204903
  rw [data_18_204903.1, data_18_204903.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_204903 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 204903) < 262144 * m + 204903 := by
  apply descent_of_endpoint
  · rw [data_18_204903.1]; exact data_18_204903.2.2
  · rw [data_18_204903.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 204911). -/
theorem data_18_204911 : oddCount 204911 18 = 11 ∧
    acceleratedOrbit 18 204911 = 138472 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_204911 : ∀ j : Fin 18,
    204911 ≤ acceleratedOrbit j.val 204911 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_204911 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 204911) = 177147 * m + 138472 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 204911
  rw [data_18_204911.1, data_18_204911.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_204911 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 204911) < 262144 * m + 204911 := by
  apply descent_of_endpoint
  · rw [data_18_204911.1]; exact data_18_204911.2.2
  · rw [data_18_204911.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 205023). -/
theorem data_18_205023 : oddCount 205023 18 = 11 ∧
    acceleratedOrbit 18 205023 = 138548 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_205023 : ∀ j : Fin 18,
    205023 ≤ acceleratedOrbit j.val 205023 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_205023 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 205023) = 177147 * m + 138548 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 205023
  rw [data_18_205023.1, data_18_205023.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_205023 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 205023) < 262144 * m + 205023 := by
  apply descent_of_endpoint
  · rw [data_18_205023.1]; exact data_18_205023.2.2
  · rw [data_18_205023.2.1]; decide

end Collatz.Research.FirstDescent.Batch193
