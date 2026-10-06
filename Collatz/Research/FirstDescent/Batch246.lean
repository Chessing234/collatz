import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 246. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch246
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 72807). -/
theorem data_20_72807 : oddCount 72807 20 = 12 ∧
    acceleratedOrbit 20 72807 = 36901 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_72807 : ∀ j : Fin 20,
    72807 ≤ acceleratedOrbit j.val 72807 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_72807 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 72807) = 531441 * m + 36901 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 72807
  rw [data_20_72807.1, data_20_72807.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_72807 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 72807) < 1048576 * m + 72807 := by
  apply descent_of_endpoint
  · rw [data_20_72807.1]; exact data_20_72807.2.2
  · rw [data_20_72807.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 72815). -/
theorem data_20_72815 : oddCount 72815 20 = 12 ∧
    acceleratedOrbit 20 72815 = 36905 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_72815 : ∀ j : Fin 20,
    72815 ≤ acceleratedOrbit j.val 72815 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_72815 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 72815) = 531441 * m + 36905 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 72815
  rw [data_20_72815.1, data_20_72815.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_72815 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 72815) < 1048576 * m + 72815 := by
  apply descent_of_endpoint
  · rw [data_20_72815.1]; exact data_20_72815.2.2
  · rw [data_20_72815.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 73791). -/
theorem data_20_73791 : oddCount 73791 20 = 12 ∧
    acceleratedOrbit 20 73791 = 37400 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_73791 : ∀ j : Fin 20,
    73791 ≤ acceleratedOrbit j.val 73791 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_73791 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 73791) = 531441 * m + 37400 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 73791
  rw [data_20_73791.1, data_20_73791.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_73791 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 73791) < 1048576 * m + 73791 := by
  apply descent_of_endpoint
  · rw [data_20_73791.1]; exact data_20_73791.2.2
  · rw [data_20_73791.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 73819). -/
theorem data_20_73819 : oddCount 73819 20 = 12 ∧
    acceleratedOrbit 20 73819 = 37414 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_73819 : ∀ j : Fin 20,
    73819 ≤ acceleratedOrbit j.val 73819 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_73819 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 73819) = 531441 * m + 37414 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 73819
  rw [data_20_73819.1, data_20_73819.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_73819 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 73819) < 1048576 * m + 73819 := by
  apply descent_of_endpoint
  · rw [data_20_73819.1]; exact data_20_73819.2.2
  · rw [data_20_73819.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 73839). -/
theorem data_20_73839 : oddCount 73839 20 = 12 ∧
    acceleratedOrbit 20 73839 = 37424 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_73839 : ∀ j : Fin 20,
    73839 ≤ acceleratedOrbit j.val 73839 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_73839 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 73839) = 531441 * m + 37424 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 73839
  rw [data_20_73839.1, data_20_73839.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_73839 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 73839) < 1048576 * m + 73839 := by
  apply descent_of_endpoint
  · rw [data_20_73839.1]; exact data_20_73839.2.2
  · rw [data_20_73839.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 73951). -/
theorem data_20_73951 : oddCount 73951 20 = 12 ∧
    acceleratedOrbit 20 73951 = 37481 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_73951 : ∀ j : Fin 20,
    73951 ≤ acceleratedOrbit j.val 73951 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_73951 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 73951) = 531441 * m + 37481 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 73951
  rw [data_20_73951.1, data_20_73951.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_73951 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 73951) < 1048576 * m + 73951 := by
  apply descent_of_endpoint
  · rw [data_20_73951.1]; exact data_20_73951.2.2
  · rw [data_20_73951.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 74395). -/
theorem data_20_74395 : oddCount 74395 20 = 12 ∧
    acceleratedOrbit 20 74395 = 37706 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_74395 : ∀ j : Fin 20,
    74395 ≤ acceleratedOrbit j.val 74395 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_74395 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 74395) = 531441 * m + 37706 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 74395
  rw [data_20_74395.1, data_20_74395.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_74395 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 74395) < 1048576 * m + 74395 := by
  apply descent_of_endpoint
  · rw [data_20_74395.1]; exact data_20_74395.2.2
  · rw [data_20_74395.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 74559). -/
theorem data_20_74559 : oddCount 74559 20 = 12 ∧
    acceleratedOrbit 20 74559 = 37789 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_74559 : ∀ j : Fin 20,
    74559 ≤ acceleratedOrbit j.val 74559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_74559 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 74559) = 531441 * m + 37789 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 74559
  rw [data_20_74559.1, data_20_74559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_74559 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 74559) < 1048576 * m + 74559 := by
  apply descent_of_endpoint
  · rw [data_20_74559.1]; exact data_20_74559.2.2
  · rw [data_20_74559.2.1]; decide

end Collatz.Research.FirstDescent.Batch246
