import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 37. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch037
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 27291). -/
theorem data_15_27291 : oddCount 27291 15 = 9 ∧
    acceleratedOrbit 15 27291 = 16394 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_27291 : ∀ j : Fin 15,
    27291 ≤ acceleratedOrbit j.val 27291 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_27291 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 27291) = 19683 * m + 16394 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 27291
  rw [data_15_27291.1, data_15_27291.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_27291 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 27291) < 32768 * m + 27291 := by
  apply descent_of_endpoint
  · rw [data_15_27291.1]; exact data_15_27291.2.2
  · rw [data_15_27291.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 27759). -/
theorem data_15_27759 : oddCount 27759 15 = 9 ∧
    acceleratedOrbit 15 27759 = 16675 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_27759 : ∀ j : Fin 15,
    27759 ≤ acceleratedOrbit j.val 27759 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_27759 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 27759) = 19683 * m + 16675 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 27759
  rw [data_15_27759.1, data_15_27759.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_27759 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 27759) < 32768 * m + 27759 := by
  apply descent_of_endpoint
  · rw [data_15_27759.1]; exact data_15_27759.2.2
  · rw [data_15_27759.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 27839). -/
theorem data_15_27839 : oddCount 27839 15 = 9 ∧
    acceleratedOrbit 15 27839 = 16723 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_27839 : ∀ j : Fin 15,
    27839 ≤ acceleratedOrbit j.val 27839 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_27839 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 27839) = 19683 * m + 16723 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 27839
  rw [data_15_27839.1, data_15_27839.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_27839 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 27839) < 32768 * m + 27839 := by
  apply descent_of_endpoint
  · rw [data_15_27839.1]; exact data_15_27839.2.2
  · rw [data_15_27839.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 27855). -/
theorem data_15_27855 : oddCount 27855 15 = 9 ∧
    acceleratedOrbit 15 27855 = 16733 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_27855 : ∀ j : Fin 15,
    27855 ≤ acceleratedOrbit j.val 27855 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_27855 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 27855) = 19683 * m + 16733 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 27855
  rw [data_15_27855.1, data_15_27855.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_27855 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 27855) < 32768 * m + 27855 := by
  apply descent_of_endpoint
  · rw [data_15_27855.1]; exact data_15_27855.2.2
  · rw [data_15_27855.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 27975). -/
theorem data_15_27975 : oddCount 27975 15 = 9 ∧
    acceleratedOrbit 15 27975 = 16805 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_27975 : ∀ j : Fin 15,
    27975 ≤ acceleratedOrbit j.val 27975 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_27975 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 27975) = 19683 * m + 16805 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 27975
  rw [data_15_27975.1, data_15_27975.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_27975 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 27975) < 32768 * m + 27975 := by
  apply descent_of_endpoint
  · rw [data_15_27975.1]; exact data_15_27975.2.2
  · rw [data_15_27975.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 28703). -/
theorem data_15_28703 : oddCount 28703 15 = 9 ∧
    acceleratedOrbit 15 28703 = 17242 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_28703 : ∀ j : Fin 15,
    28703 ≤ acceleratedOrbit j.val 28703 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_28703 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 28703) = 19683 * m + 17242 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 28703
  rw [data_15_28703.1, data_15_28703.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_28703 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 28703) < 32768 * m + 28703 := by
  apply descent_of_endpoint
  · rw [data_15_28703.1]; exact data_15_28703.2.2
  · rw [data_15_28703.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 28879). -/
theorem data_15_28879 : oddCount 28879 15 = 9 ∧
    acceleratedOrbit 15 28879 = 17348 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_28879 : ∀ j : Fin 15,
    28879 ≤ acceleratedOrbit j.val 28879 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_28879 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 28879) = 19683 * m + 17348 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 28879
  rw [data_15_28879.1, data_15_28879.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_28879 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 28879) < 32768 * m + 28879 := by
  apply descent_of_endpoint
  · rw [data_15_28879.1]; exact data_15_28879.2.2
  · rw [data_15_28879.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 28999). -/
theorem data_15_28999 : oddCount 28999 15 = 9 ∧
    acceleratedOrbit 15 28999 = 17420 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_28999 : ∀ j : Fin 15,
    28999 ≤ acceleratedOrbit j.val 28999 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_28999 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 28999) = 19683 * m + 17420 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 28999
  rw [data_15_28999.1, data_15_28999.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_28999 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 28999) < 32768 * m + 28999 := by
  apply descent_of_endpoint
  · rw [data_15_28999.1]; exact data_15_28999.2.2
  · rw [data_15_28999.2.1]; decide

end Collatz.Research.FirstDescent.Batch037
