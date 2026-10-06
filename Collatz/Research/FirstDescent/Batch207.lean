import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 207. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch207
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 232263). -/
theorem data_18_232263 : oddCount 232263 18 = 11 ∧
    acceleratedOrbit 18 232263 = 156956 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_232263 : ∀ j : Fin 18,
    232263 ≤ acceleratedOrbit j.val 232263 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_232263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 232263) = 177147 * m + 156956 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 232263
  rw [data_18_232263.1, data_18_232263.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_232263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 232263) < 262144 * m + 232263 := by
  apply descent_of_endpoint
  · rw [data_18_232263.1]; exact data_18_232263.2.2
  · rw [data_18_232263.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 232303). -/
theorem data_18_232303 : oddCount 232303 18 = 11 ∧
    acceleratedOrbit 18 232303 = 156983 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_232303 : ∀ j : Fin 18,
    232303 ≤ acceleratedOrbit j.val 232303 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_232303 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 232303) = 177147 * m + 156983 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 232303
  rw [data_18_232303.1, data_18_232303.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_232303 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 232303) < 262144 * m + 232303 := by
  apply descent_of_endpoint
  · rw [data_18_232303.1]; exact data_18_232303.2.2
  · rw [data_18_232303.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 232863). -/
theorem data_18_232863 : oddCount 232863 18 = 11 ∧
    acceleratedOrbit 18 232863 = 157361 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_232863 : ∀ j : Fin 18,
    232863 ≤ acceleratedOrbit j.val 232863 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_232863 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 232863) = 177147 * m + 157361 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 232863
  rw [data_18_232863.1, data_18_232863.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_232863 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 232863) < 262144 * m + 232863 := by
  apply descent_of_endpoint
  · rw [data_18_232863.1]; exact data_18_232863.2.2
  · rw [data_18_232863.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 232911). -/
theorem data_18_232911 : oddCount 232911 18 = 11 ∧
    acceleratedOrbit 18 232911 = 157394 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_232911 : ∀ j : Fin 18,
    232911 ≤ acceleratedOrbit j.val 232911 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_232911 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 232911) = 177147 * m + 157394 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 232911
  rw [data_18_232911.1, data_18_232911.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_232911 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 232911) < 262144 * m + 232911 := by
  apply descent_of_endpoint
  · rw [data_18_232911.1]; exact data_18_232911.2.2
  · rw [data_18_232911.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 232943). -/
theorem data_18_232943 : oddCount 232943 18 = 11 ∧
    acceleratedOrbit 18 232943 = 157415 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_232943 : ∀ j : Fin 18,
    232943 ≤ acceleratedOrbit j.val 232943 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_232943 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 232943) = 177147 * m + 157415 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 232943
  rw [data_18_232943.1, data_18_232943.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_232943 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 232943) < 262144 * m + 232943 := by
  apply descent_of_endpoint
  · rw [data_18_232943.1]; exact data_18_232943.2.2
  · rw [data_18_232943.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 233071). -/
theorem data_18_233071 : oddCount 233071 18 = 11 ∧
    acceleratedOrbit 18 233071 = 157502 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_233071 : ∀ j : Fin 18,
    233071 ≤ acceleratedOrbit j.val 233071 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_233071 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 233071) = 177147 * m + 157502 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 233071
  rw [data_18_233071.1, data_18_233071.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_233071 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 233071) < 262144 * m + 233071 := by
  apply descent_of_endpoint
  · rw [data_18_233071.1]; exact data_18_233071.2.2
  · rw [data_18_233071.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 233191). -/
theorem data_18_233191 : oddCount 233191 18 = 11 ∧
    acceleratedOrbit 18 233191 = 157583 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_233191 : ∀ j : Fin 18,
    233191 ≤ acceleratedOrbit j.val 233191 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_233191 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 233191) = 177147 * m + 157583 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 233191
  rw [data_18_233191.1, data_18_233191.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_233191 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 233191) < 262144 * m + 233191 := by
  apply descent_of_endpoint
  · rw [data_18_233191.1]; exact data_18_233191.2.2
  · rw [data_18_233191.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 233199). -/
theorem data_18_233199 : oddCount 233199 18 = 11 ∧
    acceleratedOrbit 18 233199 = 157588 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_233199 : ∀ j : Fin 18,
    233199 ≤ acceleratedOrbit j.val 233199 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_233199 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 233199) = 177147 * m + 157588 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 233199
  rw [data_18_233199.1, data_18_233199.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_233199 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 233199) < 262144 * m + 233199 := by
  apply descent_of_endpoint
  · rw [data_18_233199.1]; exact data_18_233199.2.2
  · rw [data_18_233199.2.1]; decide

end Collatz.Research.FirstDescent.Batch207
