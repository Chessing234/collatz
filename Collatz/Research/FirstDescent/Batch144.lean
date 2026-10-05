import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 144. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch144
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 95263). -/
theorem data_18_95263 : oddCount 95263 18 = 11 ∧
    acceleratedOrbit 18 95263 = 64376 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_95263 : ∀ j : Fin 18,
    95263 ≤ acceleratedOrbit j.val 95263 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_95263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 95263) = 177147 * m + 64376 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 95263
  rw [data_18_95263.1, data_18_95263.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_95263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 95263) < 262144 * m + 95263 := by
  apply descent_of_endpoint
  · rw [data_18_95263.1]; exact data_18_95263.2.2
  · rw [data_18_95263.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 95711). -/
theorem data_18_95711 : oddCount 95711 18 = 11 ∧
    acceleratedOrbit 18 95711 = 64679 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_95711 : ∀ j : Fin 18,
    95711 ≤ acceleratedOrbit j.val 95711 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_95711 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 95711) = 177147 * m + 64679 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 95711
  rw [data_18_95711.1, data_18_95711.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_95711 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 95711) < 262144 * m + 95711 := by
  apply descent_of_endpoint
  · rw [data_18_95711.1]; exact data_18_95711.2.2
  · rw [data_18_95711.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 95791). -/
theorem data_18_95791 : oddCount 95791 18 = 11 ∧
    acceleratedOrbit 18 95791 = 64733 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_95791 : ∀ j : Fin 18,
    95791 ≤ acceleratedOrbit j.val 95791 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_95791 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 95791) = 177147 * m + 64733 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 95791
  rw [data_18_95791.1, data_18_95791.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_95791 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 95791) < 262144 * m + 95791 := by
  apply descent_of_endpoint
  · rw [data_18_95791.1]; exact data_18_95791.2.2
  · rw [data_18_95791.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 96319). -/
theorem data_18_96319 : oddCount 96319 18 = 11 ∧
    acceleratedOrbit 18 96319 = 65090 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_96319 : ∀ j : Fin 18,
    96319 ≤ acceleratedOrbit j.val 96319 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_96319 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 96319) = 177147 * m + 65090 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 96319
  rw [data_18_96319.1, data_18_96319.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_96319 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 96319) < 262144 * m + 96319 := by
  apply descent_of_endpoint
  · rw [data_18_96319.1]; exact data_18_96319.2.2
  · rw [data_18_96319.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 96359). -/
theorem data_18_96359 : oddCount 96359 18 = 11 ∧
    acceleratedOrbit 18 96359 = 65117 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_96359 : ∀ j : Fin 18,
    96359 ≤ acceleratedOrbit j.val 96359 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_96359 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 96359) = 177147 * m + 65117 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 96359
  rw [data_18_96359.1, data_18_96359.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_96359 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 96359) < 262144 * m + 96359 := by
  apply descent_of_endpoint
  · rw [data_18_96359.1]; exact data_18_96359.2.2
  · rw [data_18_96359.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 96923). -/
theorem data_18_96923 : oddCount 96923 18 = 11 ∧
    acceleratedOrbit 18 96923 = 65498 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_96923 : ∀ j : Fin 18,
    96923 ≤ acceleratedOrbit j.val 96923 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_96923 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 96923) = 177147 * m + 65498 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 96923
  rw [data_18_96923.1, data_18_96923.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_96923 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 96923) < 262144 * m + 96923 := by
  apply descent_of_endpoint
  · rw [data_18_96923.1]; exact data_18_96923.2.2
  · rw [data_18_96923.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 97343). -/
theorem data_18_97343 : oddCount 97343 18 = 11 ∧
    acceleratedOrbit 18 97343 = 65782 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_97343 : ∀ j : Fin 18,
    97343 ≤ acceleratedOrbit j.val 97343 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_97343 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 97343) = 177147 * m + 65782 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 97343
  rw [data_18_97343.1, data_18_97343.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_97343 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 97343) < 262144 * m + 97343 := by
  apply descent_of_endpoint
  · rw [data_18_97343.1]; exact data_18_97343.2.2
  · rw [data_18_97343.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 97663). -/
theorem data_18_97663 : oddCount 97663 18 = 11 ∧
    acceleratedOrbit 18 97663 = 65998 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_97663 : ∀ j : Fin 18,
    97663 ≤ acceleratedOrbit j.val 97663 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_97663 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 97663) = 177147 * m + 65998 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 97663
  rw [data_18_97663.1, data_18_97663.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_97663 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 97663) < 262144 * m + 97663 := by
  apply descent_of_endpoint
  · rw [data_18_97663.1]; exact data_18_97663.2.2
  · rw [data_18_97663.2.1]; decide

end Collatz.Research.FirstDescent.Batch144
