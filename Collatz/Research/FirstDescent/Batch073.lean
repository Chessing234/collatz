import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 73. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch073
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 36543). -/
theorem data_16_36543 : oddCount 36543 16 = 10 ∧
    acceleratedOrbit 16 36543 = 32927 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_36543 : ∀ j : Fin 16,
    36543 ≤ acceleratedOrbit j.val 36543 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_36543 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 36543) = 59049 * m + 32927 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 36543
  rw [data_16_36543.1, data_16_36543.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_36543 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 36543) < 65536 * m + 36543 := by
  apply descent_of_endpoint
  · rw [data_16_36543.1]; exact data_16_36543.2.2
  · rw [data_16_36543.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 36635). -/
theorem data_16_36635 : oddCount 36635 16 = 10 ∧
    acceleratedOrbit 16 36635 = 33010 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_36635 : ∀ j : Fin 16,
    36635 ≤ acceleratedOrbit j.val 36635 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_36635 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 36635) = 59049 * m + 33010 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 36635
  rw [data_16_36635.1, data_16_36635.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_36635 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 36635) < 65536 * m + 36635 := by
  apply descent_of_endpoint
  · rw [data_16_36635.1]; exact data_16_36635.2.2
  · rw [data_16_36635.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 36639). -/
theorem data_16_36639 : oddCount 36639 16 = 10 ∧
    acceleratedOrbit 16 36639 = 33014 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_36639 : ∀ j : Fin 16,
    36639 ≤ acceleratedOrbit j.val 36639 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_36639 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 36639) = 59049 * m + 33014 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 36639
  rw [data_16_36639.1, data_16_36639.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_36639 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 36639) < 65536 * m + 36639 := by
  apply descent_of_endpoint
  · rw [data_16_36639.1]; exact data_16_36639.2.2
  · rw [data_16_36639.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 36719). -/
theorem data_16_36719 : oddCount 36719 16 = 10 ∧
    acceleratedOrbit 16 36719 = 33086 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_36719 : ∀ j : Fin 16,
    36719 ≤ acceleratedOrbit j.val 36719 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_36719 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 36719) = 59049 * m + 33086 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 36719
  rw [data_16_36719.1, data_16_36719.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_36719 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 36719) < 65536 * m + 36719 := by
  apply descent_of_endpoint
  · rw [data_16_36719.1]; exact data_16_36719.2.2
  · rw [data_16_36719.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 36891). -/
theorem data_16_36891 : oddCount 36891 16 = 10 ∧
    acceleratedOrbit 16 36891 = 33241 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_36891 : ∀ j : Fin 16,
    36891 ≤ acceleratedOrbit j.val 36891 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_36891 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 36891) = 59049 * m + 33241 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 36891
  rw [data_16_36891.1, data_16_36891.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_36891 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 36891) < 65536 * m + 36891 := by
  apply descent_of_endpoint
  · rw [data_16_36891.1]; exact data_16_36891.2.2
  · rw [data_16_36891.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 36911). -/
theorem data_16_36911 : oddCount 36911 16 = 10 ∧
    acceleratedOrbit 16 36911 = 33259 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_36911 : ∀ j : Fin 16,
    36911 ≤ acceleratedOrbit j.val 36911 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_36911 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 36911) = 59049 * m + 33259 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 36911
  rw [data_16_36911.1, data_16_36911.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_36911 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 36911) < 65536 * m + 36911 := by
  apply descent_of_endpoint
  · rw [data_16_36911.1]; exact data_16_36911.2.2
  · rw [data_16_36911.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 37119). -/
theorem data_16_37119 : oddCount 37119 16 = 10 ∧
    acceleratedOrbit 16 37119 = 33446 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_37119 : ∀ j : Fin 16,
    37119 ≤ acceleratedOrbit j.val 37119 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_37119 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 37119) = 59049 * m + 33446 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 37119
  rw [data_16_37119.1, data_16_37119.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_37119 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 37119) < 65536 * m + 37119 := by
  apply descent_of_endpoint
  · rw [data_16_37119.1]; exact data_16_37119.2.2
  · rw [data_16_37119.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 37167). -/
theorem data_16_37167 : oddCount 37167 16 = 10 ∧
    acceleratedOrbit 16 37167 = 33490 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_37167 : ∀ j : Fin 16,
    37167 ≤ acceleratedOrbit j.val 37167 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_37167 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 37167) = 59049 * m + 33490 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 37167
  rw [data_16_37167.1, data_16_37167.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_37167 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 37167) < 65536 * m + 37167 := by
  apply descent_of_endpoint
  · rw [data_16_37167.1]; exact data_16_37167.2.2
  · rw [data_16_37167.2.1]; decide

end Collatz.Research.FirstDescent.Batch073
