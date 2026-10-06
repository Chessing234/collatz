import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 121. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch121
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 48191). -/
theorem data_18_48191 : oddCount 48191 18 = 11 ∧
    acceleratedOrbit 18 48191 = 32567 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_48191 : ∀ j : Fin 18,
    48191 ≤ acceleratedOrbit j.val 48191 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_48191 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 48191) = 177147 * m + 32567 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 48191
  rw [data_18_48191.1, data_18_48191.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_48191 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 48191) < 262144 * m + 48191 := by
  apply descent_of_endpoint
  · rw [data_18_48191.1]; exact data_18_48191.2.2
  · rw [data_18_48191.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 48431). -/
theorem data_18_48431 : oddCount 48431 18 = 11 ∧
    acceleratedOrbit 18 48431 = 32729 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_48431 : ∀ j : Fin 18,
    48431 ≤ acceleratedOrbit j.val 48431 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_48431 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 48431) = 177147 * m + 32729 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 48431
  rw [data_18_48431.1, data_18_48431.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_48431 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 48431) < 262144 * m + 48431 := by
  apply descent_of_endpoint
  · rw [data_18_48431.1]; exact data_18_48431.2.2
  · rw [data_18_48431.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 48511). -/
theorem data_18_48511 : oddCount 48511 18 = 11 ∧
    acceleratedOrbit 18 48511 = 32783 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_48511 : ∀ j : Fin 18,
    48511 ≤ acceleratedOrbit j.val 48511 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_48511 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 48511) = 177147 * m + 32783 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 48511
  rw [data_18_48511.1, data_18_48511.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_48511 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 48511) < 262144 * m + 48511 := by
  apply descent_of_endpoint
  · rw [data_18_48511.1]; exact data_18_48511.2.2
  · rw [data_18_48511.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 48671). -/
theorem data_18_48671 : oddCount 48671 18 = 11 ∧
    acceleratedOrbit 18 48671 = 32891 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_48671 : ∀ j : Fin 18,
    48671 ≤ acceleratedOrbit j.val 48671 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_48671 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 48671) = 177147 * m + 32891 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 48671
  rw [data_18_48671.1, data_18_48671.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_48671 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 48671) < 262144 * m + 48671 := by
  apply descent_of_endpoint
  · rw [data_18_48671.1]; exact data_18_48671.2.2
  · rw [data_18_48671.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 48831). -/
theorem data_18_48831 : oddCount 48831 18 = 11 ∧
    acceleratedOrbit 18 48831 = 32999 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_48831 : ∀ j : Fin 18,
    48831 ≤ acceleratedOrbit j.val 48831 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_48831 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 48831) = 177147 * m + 32999 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 48831
  rw [data_18_48831.1, data_18_48831.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_48831 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 48831) < 262144 * m + 48831 := by
  apply descent_of_endpoint
  · rw [data_18_48831.1]; exact data_18_48831.2.2
  · rw [data_18_48831.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 48847). -/
theorem data_18_48847 : oddCount 48847 18 = 11 ∧
    acceleratedOrbit 18 48847 = 33010 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_48847 : ∀ j : Fin 18,
    48847 ≤ acceleratedOrbit j.val 48847 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_48847 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 48847) = 177147 * m + 33010 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 48847
  rw [data_18_48847.1, data_18_48847.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_48847 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 48847) < 262144 * m + 48847 := by
  apply descent_of_endpoint
  · rw [data_18_48847.1]; exact data_18_48847.2.2
  · rw [data_18_48847.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 48959). -/
theorem data_18_48959 : oddCount 48959 18 = 11 ∧
    acceleratedOrbit 18 48959 = 33086 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_48959 : ∀ j : Fin 18,
    48959 ≤ acceleratedOrbit j.val 48959 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_48959 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 48959) = 177147 * m + 33086 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 48959
  rw [data_18_48959.1, data_18_48959.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_48959 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 48959) < 262144 * m + 48959 := by
  apply descent_of_endpoint
  · rw [data_18_48959.1]; exact data_18_48959.2.2
  · rw [data_18_48959.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 49087). -/
theorem data_18_49087 : oddCount 49087 18 = 11 ∧
    acceleratedOrbit 18 49087 = 33172 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_49087 : ∀ j : Fin 18,
    49087 ≤ acceleratedOrbit j.val 49087 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_49087 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 49087) = 177147 * m + 33172 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 49087
  rw [data_18_49087.1, data_18_49087.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_49087 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 49087) < 262144 * m + 49087 := by
  apply descent_of_endpoint
  · rw [data_18_49087.1]; exact data_18_49087.2.2
  · rw [data_18_49087.2.1]; decide

end Collatz.Research.FirstDescent.Batch121
