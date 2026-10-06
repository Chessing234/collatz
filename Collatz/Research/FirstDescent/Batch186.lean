import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 186. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch186
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 183655). -/
theorem data_18_183655 : oddCount 183655 18 = 11 ∧
    acceleratedOrbit 18 183655 = 124108 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_183655 : ∀ j : Fin 18,
    183655 ≤ acceleratedOrbit j.val 183655 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_183655 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 183655) = 177147 * m + 124108 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 183655
  rw [data_18_183655.1, data_18_183655.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_183655 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 183655) < 262144 * m + 183655 := by
  apply descent_of_endpoint
  · rw [data_18_183655.1]; exact data_18_183655.2.2
  · rw [data_18_183655.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 183967). -/
theorem data_18_183967 : oddCount 183967 18 = 11 ∧
    acceleratedOrbit 18 183967 = 124319 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_183967 : ∀ j : Fin 18,
    183967 ≤ acceleratedOrbit j.val 183967 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_183967 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 183967) = 177147 * m + 124319 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 183967
  rw [data_18_183967.1, data_18_183967.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_183967 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 183967) < 262144 * m + 183967 := by
  apply descent_of_endpoint
  · rw [data_18_183967.1]; exact data_18_183967.2.2
  · rw [data_18_183967.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 184047). -/
theorem data_18_184047 : oddCount 184047 18 = 11 ∧
    acceleratedOrbit 18 184047 = 124373 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_184047 : ∀ j : Fin 18,
    184047 ≤ acceleratedOrbit j.val 184047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_184047 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 184047) = 177147 * m + 124373 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 184047
  rw [data_18_184047.1, data_18_184047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_184047 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 184047) < 262144 * m + 184047 := by
  apply descent_of_endpoint
  · rw [data_18_184047.1]; exact data_18_184047.2.2
  · rw [data_18_184047.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 185191). -/
theorem data_18_185191 : oddCount 185191 18 = 11 ∧
    acceleratedOrbit 18 185191 = 125146 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_185191 : ∀ j : Fin 18,
    185191 ≤ acceleratedOrbit j.val 185191 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_185191 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 185191) = 177147 * m + 125146 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 185191
  rw [data_18_185191.1, data_18_185191.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_185191 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 185191) < 262144 * m + 185191 := by
  apply descent_of_endpoint
  · rw [data_18_185191.1]; exact data_18_185191.2.2
  · rw [data_18_185191.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 185703). -/
theorem data_18_185703 : oddCount 185703 18 = 11 ∧
    acceleratedOrbit 18 185703 = 125492 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_185703 : ∀ j : Fin 18,
    185703 ≤ acceleratedOrbit j.val 185703 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_185703 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 185703) = 177147 * m + 125492 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 185703
  rw [data_18_185703.1, data_18_185703.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_185703 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 185703) < 262144 * m + 185703 := by
  apply descent_of_endpoint
  · rw [data_18_185703.1]; exact data_18_185703.2.2
  · rw [data_18_185703.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 185883). -/
theorem data_18_185883 : oddCount 185883 18 = 11 ∧
    acceleratedOrbit 18 185883 = 125614 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_185883 : ∀ j : Fin 18,
    185883 ≤ acceleratedOrbit j.val 185883 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_185883 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 185883) = 177147 * m + 125614 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 185883
  rw [data_18_185883.1, data_18_185883.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_185883 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 185883) < 262144 * m + 185883 := by
  apply descent_of_endpoint
  · rw [data_18_185883.1]; exact data_18_185883.2.2
  · rw [data_18_185883.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 185983). -/
theorem data_18_185983 : oddCount 185983 18 = 11 ∧
    acceleratedOrbit 18 185983 = 125681 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_185983 : ∀ j : Fin 18,
    185983 ≤ acceleratedOrbit j.val 185983 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_185983 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 185983) = 177147 * m + 125681 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 185983
  rw [data_18_185983.1, data_18_185983.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_185983 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 185983) < 262144 * m + 185983 := by
  apply descent_of_endpoint
  · rw [data_18_185983.1]; exact data_18_185983.2.2
  · rw [data_18_185983.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 186395). -/
theorem data_18_186395 : oddCount 186395 18 = 11 ∧
    acceleratedOrbit 18 186395 = 125960 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_186395 : ∀ j : Fin 18,
    186395 ≤ acceleratedOrbit j.val 186395 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_186395 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 186395) = 177147 * m + 125960 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 186395
  rw [data_18_186395.1, data_18_186395.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_186395 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 186395) < 262144 * m + 186395 := by
  apply descent_of_endpoint
  · rw [data_18_186395.1]; exact data_18_186395.2.2
  · rw [data_18_186395.2.1]; decide

end Collatz.Research.FirstDescent.Batch186
