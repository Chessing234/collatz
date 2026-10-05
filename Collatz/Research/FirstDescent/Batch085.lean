import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 85. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch085
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 50143). -/
theorem data_16_50143 : oddCount 50143 16 = 10 ∧
    acceleratedOrbit 16 50143 = 45181 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_50143 : ∀ j : Fin 16,
    50143 ≤ acceleratedOrbit j.val 50143 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_50143 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 50143) = 59049 * m + 45181 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 50143
  rw [data_16_50143.1, data_16_50143.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_50143 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 50143) < 65536 * m + 50143 := by
  apply descent_of_endpoint
  · rw [data_16_50143.1]; exact data_16_50143.2.2
  · rw [data_16_50143.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 50267). -/
theorem data_16_50267 : oddCount 50267 16 = 10 ∧
    acceleratedOrbit 16 50267 = 45293 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_50267 : ∀ j : Fin 16,
    50267 ≤ acceleratedOrbit j.val 50267 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_50267 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 50267) = 59049 * m + 45293 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 50267
  rw [data_16_50267.1, data_16_50267.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_50267 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 50267) < 65536 * m + 50267 := by
  apply descent_of_endpoint
  · rw [data_16_50267.1]; exact data_16_50267.2.2
  · rw [data_16_50267.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 50303). -/
theorem data_16_50303 : oddCount 50303 16 = 10 ∧
    acceleratedOrbit 16 50303 = 45325 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_50303 : ∀ j : Fin 16,
    50303 ≤ acceleratedOrbit j.val 50303 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_50303 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 50303) = 59049 * m + 45325 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 50303
  rw [data_16_50303.1, data_16_50303.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_50303 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 50303) < 65536 * m + 50303 := by
  apply descent_of_endpoint
  · rw [data_16_50303.1]; exact data_16_50303.2.2
  · rw [data_16_50303.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 50407). -/
theorem data_16_50407 : oddCount 50407 16 = 10 ∧
    acceleratedOrbit 16 50407 = 45419 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_50407 : ∀ j : Fin 16,
    50407 ≤ acceleratedOrbit j.val 50407 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_50407 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 50407) = 59049 * m + 45419 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 50407
  rw [data_16_50407.1, data_16_50407.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_50407 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 50407) < 65536 * m + 50407 := by
  apply descent_of_endpoint
  · rw [data_16_50407.1]; exact data_16_50407.2.2
  · rw [data_16_50407.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 50663). -/
theorem data_16_50663 : oddCount 50663 16 = 10 ∧
    acceleratedOrbit 16 50663 = 45650 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_50663 : ∀ j : Fin 16,
    50663 ≤ acceleratedOrbit j.val 50663 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_50663 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 50663) = 59049 * m + 45650 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 50663
  rw [data_16_50663.1, data_16_50663.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_50663 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 50663) < 65536 * m + 50663 := by
  apply descent_of_endpoint
  · rw [data_16_50663.1]; exact data_16_50663.2.2
  · rw [data_16_50663.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 50843). -/
theorem data_16_50843 : oddCount 50843 16 = 10 ∧
    acceleratedOrbit 16 50843 = 45812 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_50843 : ∀ j : Fin 16,
    50843 ≤ acceleratedOrbit j.val 50843 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_50843 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 50843) = 59049 * m + 45812 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 50843
  rw [data_16_50843.1, data_16_50843.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_50843 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 50843) < 65536 * m + 50843 := by
  apply descent_of_endpoint
  · rw [data_16_50843.1]; exact data_16_50843.2.2
  · rw [data_16_50843.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 50847). -/
theorem data_16_50847 : oddCount 50847 16 = 10 ∧
    acceleratedOrbit 16 50847 = 45815 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_50847 : ∀ j : Fin 16,
    50847 ≤ acceleratedOrbit j.val 50847 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_50847 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 50847) = 59049 * m + 45815 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 50847
  rw [data_16_50847.1, data_16_50847.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_50847 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 50847) < 65536 * m + 50847 := by
  apply descent_of_endpoint
  · rw [data_16_50847.1]; exact data_16_50847.2.2
  · rw [data_16_50847.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 51055). -/
theorem data_16_51055 : oddCount 51055 16 = 10 ∧
    acceleratedOrbit 16 51055 = 46003 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_51055 : ∀ j : Fin 16,
    51055 ≤ acceleratedOrbit j.val 51055 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_51055 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 51055) = 59049 * m + 46003 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 51055
  rw [data_16_51055.1, data_16_51055.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_51055 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 51055) < 65536 * m + 51055 := by
  apply descent_of_endpoint
  · rw [data_16_51055.1]; exact data_16_51055.2.2
  · rw [data_16_51055.2.1]; decide

end Collatz.Research.FirstDescent.Batch085
