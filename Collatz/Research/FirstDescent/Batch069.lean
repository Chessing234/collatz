import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 69. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch069
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 31775). -/
theorem data_16_31775 : oddCount 31775 16 = 10 ∧
    acceleratedOrbit 16 31775 = 28631 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_31775 : ∀ j : Fin 16,
    31775 ≤ acceleratedOrbit j.val 31775 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_31775 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 31775) = 59049 * m + 28631 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 31775
  rw [data_16_31775.1, data_16_31775.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_31775 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 31775) < 65536 * m + 31775 := by
  apply descent_of_endpoint
  · rw [data_16_31775.1]; exact data_16_31775.2.2
  · rw [data_16_31775.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 32223). -/
theorem data_16_32223 : oddCount 32223 16 = 10 ∧
    acceleratedOrbit 16 32223 = 29035 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_32223 : ∀ j : Fin 16,
    32223 ≤ acceleratedOrbit j.val 32223 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_32223 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 32223) = 59049 * m + 29035 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 32223
  rw [data_16_32223.1, data_16_32223.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_32223 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 32223) < 65536 * m + 32223 := by
  apply descent_of_endpoint
  · rw [data_16_32223.1]; exact data_16_32223.2.2
  · rw [data_16_32223.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 32283). -/
theorem data_16_32283 : oddCount 32283 16 = 10 ∧
    acceleratedOrbit 16 32283 = 29089 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_32283 : ∀ j : Fin 16,
    32283 ≤ acceleratedOrbit j.val 32283 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_32283 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 32283) = 59049 * m + 29089 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 32283
  rw [data_16_32283.1, data_16_32283.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_32283 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 32283) < 65536 * m + 32283 := by
  apply descent_of_endpoint
  · rw [data_16_32283.1]; exact data_16_32283.2.2
  · rw [data_16_32283.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 32303). -/
theorem data_16_32303 : oddCount 32303 16 = 10 ∧
    acceleratedOrbit 16 32303 = 29107 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_32303 : ∀ j : Fin 16,
    32303 ≤ acceleratedOrbit j.val 32303 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_32303 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 32303) = 59049 * m + 29107 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 32303
  rw [data_16_32303.1, data_16_32303.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_32303 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 32303) < 65536 * m + 32303 := by
  apply descent_of_endpoint
  · rw [data_16_32303.1]; exact data_16_32303.2.2
  · rw [data_16_32303.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 32703). -/
theorem data_16_32703 : oddCount 32703 16 = 10 ∧
    acceleratedOrbit 16 32703 = 29467 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_32703 : ∀ j : Fin 16,
    32703 ≤ acceleratedOrbit j.val 32703 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_32703 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 32703) = 59049 * m + 29467 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 32703
  rw [data_16_32703.1, data_16_32703.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_32703 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 32703) < 65536 * m + 32703 := by
  apply descent_of_endpoint
  · rw [data_16_32703.1]; exact data_16_32703.2.2
  · rw [data_16_32703.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 32763). -/
theorem data_16_32763 : oddCount 32763 16 = 10 ∧
    acceleratedOrbit 16 32763 = 29522 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_32763 : ∀ j : Fin 16,
    32763 ≤ acceleratedOrbit j.val 32763 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_32763 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 32763) = 59049 * m + 29522 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 32763
  rw [data_16_32763.1, data_16_32763.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_32763 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 32763) < 65536 * m + 32763 := by
  apply descent_of_endpoint
  · rw [data_16_32763.1]; exact data_16_32763.2.2
  · rw [data_16_32763.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 32859). -/
theorem data_16_32859 : oddCount 32859 16 = 10 ∧
    acceleratedOrbit 16 32859 = 29608 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_32859 : ∀ j : Fin 16,
    32859 ≤ acceleratedOrbit j.val 32859 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_32859 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 32859) = 59049 * m + 29608 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 32859
  rw [data_16_32859.1, data_16_32859.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_32859 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 32859) < 65536 * m + 32859 := by
  apply descent_of_endpoint
  · rw [data_16_32859.1]; exact data_16_32859.2.2
  · rw [data_16_32859.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 32923). -/
theorem data_16_32923 : oddCount 32923 16 = 10 ∧
    acceleratedOrbit 16 32923 = 29666 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_32923 : ∀ j : Fin 16,
    32923 ≤ acceleratedOrbit j.val 32923 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_32923 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 32923) = 59049 * m + 29666 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 32923
  rw [data_16_32923.1, data_16_32923.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_32923 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 32923) < 65536 * m + 32923 := by
  apply descent_of_endpoint
  · rw [data_16_32923.1]; exact data_16_32923.2.2
  · rw [data_16_32923.2.1]; decide

end Collatz.Research.FirstDescent.Batch069
