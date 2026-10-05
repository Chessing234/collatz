import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 36. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch036
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 25691). -/
theorem data_15_25691 : oddCount 25691 15 = 9 ∧
    acceleratedOrbit 15 25691 = 15433 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_25691 : ∀ j : Fin 15,
    25691 ≤ acceleratedOrbit j.val 25691 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_25691 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 25691) = 19683 * m + 15433 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 25691
  rw [data_15_25691.1, data_15_25691.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_25691 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 25691) < 32768 * m + 25691 := by
  apply descent_of_endpoint
  · rw [data_15_25691.1]; exact data_15_25691.2.2
  · rw [data_15_25691.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 25703). -/
theorem data_15_25703 : oddCount 25703 15 = 9 ∧
    acceleratedOrbit 15 25703 = 15440 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_25703 : ∀ j : Fin 15,
    25703 ≤ acceleratedOrbit j.val 25703 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_25703 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 25703) = 19683 * m + 15440 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 25703
  rw [data_15_25703.1, data_15_25703.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_25703 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 25703) < 32768 * m + 25703 := by
  apply descent_of_endpoint
  · rw [data_15_25703.1]; exact data_15_25703.2.2
  · rw [data_15_25703.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 25831). -/
theorem data_15_25831 : oddCount 25831 15 = 9 ∧
    acceleratedOrbit 15 25831 = 15517 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_25831 : ∀ j : Fin 15,
    25831 ≤ acceleratedOrbit j.val 25831 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_25831 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 25831) = 19683 * m + 15517 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 25831
  rw [data_15_25831.1, data_15_25831.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_25831 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 25831) < 32768 * m + 25831 := by
  apply descent_of_endpoint
  · rw [data_15_25831.1]; exact data_15_25831.2.2
  · rw [data_15_25831.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 26087). -/
theorem data_15_26087 : oddCount 26087 15 = 9 ∧
    acceleratedOrbit 15 26087 = 15671 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_26087 : ∀ j : Fin 15,
    26087 ≤ acceleratedOrbit j.val 26087 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_26087 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 26087) = 19683 * m + 15671 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 26087
  rw [data_15_26087.1, data_15_26087.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_26087 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 26087) < 32768 * m + 26087 := by
  apply descent_of_endpoint
  · rw [data_15_26087.1]; exact data_15_26087.2.2
  · rw [data_15_26087.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 26267). -/
theorem data_15_26267 : oddCount 26267 15 = 9 ∧
    acceleratedOrbit 15 26267 = 15779 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_26267 : ∀ j : Fin 15,
    26267 ≤ acceleratedOrbit j.val 26267 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_26267 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 26267) = 19683 * m + 15779 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 26267
  rw [data_15_26267.1, data_15_26267.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_26267 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 26267) < 32768 * m + 26267 := by
  apply descent_of_endpoint
  · rw [data_15_26267.1]; exact data_15_26267.2.2
  · rw [data_15_26267.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 26527). -/
theorem data_15_26527 : oddCount 26527 15 = 9 ∧
    acceleratedOrbit 15 26527 = 15935 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_26527 : ∀ j : Fin 15,
    26527 ≤ acceleratedOrbit j.val 26527 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_26527 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 26527) = 19683 * m + 15935 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 26527
  rw [data_15_26527.1, data_15_26527.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_26527 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 26527) < 32768 * m + 26527 := by
  apply descent_of_endpoint
  · rw [data_15_26527.1]; exact data_15_26527.2.2
  · rw [data_15_26527.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 26535). -/
theorem data_15_26535 : oddCount 26535 15 = 9 ∧
    acceleratedOrbit 15 26535 = 15940 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_26535 : ∀ j : Fin 15,
    26535 ≤ acceleratedOrbit j.val 26535 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_26535 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 26535) = 19683 * m + 15940 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 26535
  rw [data_15_26535.1, data_15_26535.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_26535 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 26535) < 32768 * m + 26535 := by
  apply descent_of_endpoint
  · rw [data_15_26535.1]; exact data_15_26535.2.2
  · rw [data_15_26535.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 27111). -/
theorem data_15_27111 : oddCount 27111 15 = 9 ∧
    acceleratedOrbit 15 27111 = 16286 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_27111 : ∀ j : Fin 15,
    27111 ≤ acceleratedOrbit j.val 27111 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_27111 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 27111) = 19683 * m + 16286 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 27111
  rw [data_15_27111.1, data_15_27111.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_27111 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 27111) < 32768 * m + 27111 := by
  apply descent_of_endpoint
  · rw [data_15_27111.1]; exact data_15_27111.2.2
  · rw [data_15_27111.2.1]; decide

end Collatz.Research.FirstDescent.Batch036
