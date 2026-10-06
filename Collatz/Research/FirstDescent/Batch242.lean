import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 242. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch242
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 59455). -/
theorem data_20_59455 : oddCount 59455 20 = 12 ∧
    acceleratedOrbit 20 59455 = 30134 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_59455 : ∀ j : Fin 20,
    59455 ≤ acceleratedOrbit j.val 59455 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_59455 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 59455) = 531441 * m + 30134 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 59455
  rw [data_20_59455.1, data_20_59455.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_59455 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 59455) < 1048576 * m + 59455 := by
  apply descent_of_endpoint
  · rw [data_20_59455.1]; exact data_20_59455.2.2
  · rw [data_20_59455.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 59855). -/
theorem data_20_59855 : oddCount 59855 20 = 12 ∧
    acceleratedOrbit 20 59855 = 30337 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_59855 : ∀ j : Fin 20,
    59855 ≤ acceleratedOrbit j.val 59855 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_59855 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 59855) = 531441 * m + 30337 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 59855
  rw [data_20_59855.1, data_20_59855.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_59855 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 59855) < 1048576 * m + 59855 := by
  apply descent_of_endpoint
  · rw [data_20_59855.1]; exact data_20_59855.2.2
  · rw [data_20_59855.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 59887). -/
theorem data_20_59887 : oddCount 59887 20 = 12 ∧
    acceleratedOrbit 20 59887 = 30353 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_59887 : ∀ j : Fin 20,
    59887 ≤ acceleratedOrbit j.val 59887 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_59887 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 59887) = 531441 * m + 30353 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 59887
  rw [data_20_59887.1, data_20_59887.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_59887 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 59887) < 1048576 * m + 59887 := by
  apply descent_of_endpoint
  · rw [data_20_59887.1]; exact data_20_59887.2.2
  · rw [data_20_59887.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 61087). -/
theorem data_20_61087 : oddCount 61087 20 = 12 ∧
    acceleratedOrbit 20 61087 = 30961 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_61087 : ∀ j : Fin 20,
    61087 ≤ acceleratedOrbit j.val 61087 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_61087 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 61087) = 531441 * m + 30961 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 61087
  rw [data_20_61087.1, data_20_61087.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_61087 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 61087) < 1048576 * m + 61087 := by
  apply descent_of_endpoint
  · rw [data_20_61087.1]; exact data_20_61087.2.2
  · rw [data_20_61087.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 62107). -/
theorem data_20_62107 : oddCount 62107 20 = 12 ∧
    acceleratedOrbit 20 62107 = 31478 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_62107 : ∀ j : Fin 20,
    62107 ≤ acceleratedOrbit j.val 62107 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_62107 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 62107) = 531441 * m + 31478 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 62107
  rw [data_20_62107.1, data_20_62107.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_62107 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 62107) < 1048576 * m + 62107 := by
  apply descent_of_endpoint
  · rw [data_20_62107.1]; exact data_20_62107.2.2
  · rw [data_20_62107.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 63847). -/
theorem data_20_63847 : oddCount 63847 20 = 12 ∧
    acceleratedOrbit 20 63847 = 32360 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_63847 : ∀ j : Fin 20,
    63847 ≤ acceleratedOrbit j.val 63847 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_63847 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 63847) = 531441 * m + 32360 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 63847
  rw [data_20_63847.1, data_20_63847.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_63847 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 63847) < 1048576 * m + 63847 := by
  apply descent_of_endpoint
  · rw [data_20_63847.1]; exact data_20_63847.2.2
  · rw [data_20_63847.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 64155). -/
theorem data_20_64155 : oddCount 64155 20 = 12 ∧
    acceleratedOrbit 20 64155 = 32516 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_64155 : ∀ j : Fin 20,
    64155 ≤ acceleratedOrbit j.val 64155 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_64155 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 64155) = 531441 * m + 32516 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 64155
  rw [data_20_64155.1, data_20_64155.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_64155 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 64155) < 1048576 * m + 64155 := by
  apply descent_of_endpoint
  · rw [data_20_64155.1]; exact data_20_64155.2.2
  · rw [data_20_64155.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 64575). -/
theorem data_20_64575 : oddCount 64575 20 = 12 ∧
    acceleratedOrbit 20 64575 = 32729 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_64575 : ∀ j : Fin 20,
    64575 ≤ acceleratedOrbit j.val 64575 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_64575 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 64575) = 531441 * m + 32729 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 64575
  rw [data_20_64575.1, data_20_64575.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_64575 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 64575) < 1048576 * m + 64575 := by
  apply descent_of_endpoint
  · rw [data_20_64575.1]; exact data_20_64575.2.2
  · rw [data_20_64575.2.1]; decide

end Collatz.Research.FirstDescent.Batch242
