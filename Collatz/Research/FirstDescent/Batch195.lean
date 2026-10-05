import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 195. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch195
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 208027). -/
theorem data_18_208027 : oddCount 208027 18 = 11 ∧
    acceleratedOrbit 18 208027 = 140578 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_208027 : ∀ j : Fin 18,
    208027 ≤ acceleratedOrbit j.val 208027 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_208027 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 208027) = 177147 * m + 140578 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 208027
  rw [data_18_208027.1, data_18_208027.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_208027 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 208027) < 262144 * m + 208027 := by
  apply descent_of_endpoint
  · rw [data_18_208027.1]; exact data_18_208027.2.2
  · rw [data_18_208027.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 208539). -/
theorem data_18_208539 : oddCount 208539 18 = 11 ∧
    acceleratedOrbit 18 208539 = 140924 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_208539 : ∀ j : Fin 18,
    208539 ≤ acceleratedOrbit j.val 208539 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_208539 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 208539) = 177147 * m + 140924 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 208539
  rw [data_18_208539.1, data_18_208539.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_208539 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 208539) < 262144 * m + 208539 := by
  apply descent_of_endpoint
  · rw [data_18_208539.1]; exact data_18_208539.2.2
  · rw [data_18_208539.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 208591). -/
theorem data_18_208591 : oddCount 208591 18 = 11 ∧
    acceleratedOrbit 18 208591 = 140959 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_208591 : ∀ j : Fin 18,
    208591 ≤ acceleratedOrbit j.val 208591 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_208591 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 208591) = 177147 * m + 140959 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 208591
  rw [data_18_208591.1, data_18_208591.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_208591 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 208591) < 262144 * m + 208591 := by
  apply descent_of_endpoint
  · rw [data_18_208591.1]; exact data_18_208591.2.2
  · rw [data_18_208591.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 208831). -/
theorem data_18_208831 : oddCount 208831 18 = 11 ∧
    acceleratedOrbit 18 208831 = 141121 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_208831 : ∀ j : Fin 18,
    208831 ≤ acceleratedOrbit j.val 208831 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_208831 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 208831) = 177147 * m + 141121 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 208831
  rw [data_18_208831.1, data_18_208831.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_208831 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 208831) < 262144 * m + 208831 := by
  apply descent_of_endpoint
  · rw [data_18_208831.1]; exact data_18_208831.2.2
  · rw [data_18_208831.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 208943). -/
theorem data_18_208943 : oddCount 208943 18 = 11 ∧
    acceleratedOrbit 18 208943 = 141197 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_208943 : ∀ j : Fin 18,
    208943 ≤ acceleratedOrbit j.val 208943 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_208943 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 208943) = 177147 * m + 141197 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 208943
  rw [data_18_208943.1, data_18_208943.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_208943 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 208943) < 262144 * m + 208943 := by
  apply descent_of_endpoint
  · rw [data_18_208943.1]; exact data_18_208943.2.2
  · rw [data_18_208943.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 209063). -/
theorem data_18_209063 : oddCount 209063 18 = 11 ∧
    acceleratedOrbit 18 209063 = 141278 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_209063 : ∀ j : Fin 18,
    209063 ≤ acceleratedOrbit j.val 209063 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_209063 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 209063) = 177147 * m + 141278 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 209063
  rw [data_18_209063.1, data_18_209063.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_209063 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 209063) < 262144 * m + 209063 := by
  apply descent_of_endpoint
  · rw [data_18_209063.1]; exact data_18_209063.2.2
  · rw [data_18_209063.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 209343). -/
theorem data_18_209343 : oddCount 209343 18 = 11 ∧
    acceleratedOrbit 18 209343 = 141467 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_209343 : ∀ j : Fin 18,
    209343 ≤ acceleratedOrbit j.val 209343 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_209343 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 209343) = 177147 * m + 141467 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 209343
  rw [data_18_209343.1, data_18_209343.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_209343 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 209343) < 262144 * m + 209343 := by
  apply descent_of_endpoint
  · rw [data_18_209343.1]; exact data_18_209343.2.2
  · rw [data_18_209343.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 209919). -/
theorem data_18_209919 : oddCount 209919 18 = 11 ∧
    acceleratedOrbit 18 209919 = 141856 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_209919 : ∀ j : Fin 18,
    209919 ≤ acceleratedOrbit j.val 209919 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_209919 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 209919) = 177147 * m + 141856 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 209919
  rw [data_18_209919.1, data_18_209919.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_209919 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 209919) < 262144 * m + 209919 := by
  apply descent_of_endpoint
  · rw [data_18_209919.1]; exact data_18_209919.2.2
  · rw [data_18_209919.2.1]; decide

end Collatz.Research.FirstDescent.Batch195
