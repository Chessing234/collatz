import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 67. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch067
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 29823). -/
theorem data_16_29823 : oddCount 29823 16 = 10 ∧
    acceleratedOrbit 16 29823 = 26872 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_29823 : ∀ j : Fin 16,
    29823 ≤ acceleratedOrbit j.val 29823 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_29823 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 29823) = 59049 * m + 26872 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 29823
  rw [data_16_29823.1, data_16_29823.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_29823 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 29823) < 65536 * m + 29823 := by
  apply descent_of_endpoint
  · rw [data_16_29823.1]; exact data_16_29823.2.2
  · rw [data_16_29823.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 29887). -/
theorem data_16_29887 : oddCount 29887 16 = 10 ∧
    acceleratedOrbit 16 29887 = 26930 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_29887 : ∀ j : Fin 16,
    29887 ≤ acceleratedOrbit j.val 29887 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_29887 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 29887) = 59049 * m + 26930 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 29887
  rw [data_16_29887.1, data_16_29887.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_29887 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 29887) < 65536 * m + 29887 := by
  apply descent_of_endpoint
  · rw [data_16_29887.1]; exact data_16_29887.2.2
  · rw [data_16_29887.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 30079). -/
theorem data_16_30079 : oddCount 30079 16 = 10 ∧
    acceleratedOrbit 16 30079 = 27103 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_30079 : ∀ j : Fin 16,
    30079 ≤ acceleratedOrbit j.val 30079 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_30079 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 30079) = 59049 * m + 27103 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 30079
  rw [data_16_30079.1, data_16_30079.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_30079 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 30079) < 65536 * m + 30079 := by
  apply descent_of_endpoint
  · rw [data_16_30079.1]; exact data_16_30079.2.2
  · rw [data_16_30079.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 30207). -/
theorem data_16_30207 : oddCount 30207 16 = 10 ∧
    acceleratedOrbit 16 30207 = 27218 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_30207 : ∀ j : Fin 16,
    30207 ≤ acceleratedOrbit j.val 30207 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_30207 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 30207) = 59049 * m + 27218 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 30207
  rw [data_16_30207.1, data_16_30207.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_30207 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 30207) < 65536 * m + 30207 := by
  apply descent_of_endpoint
  · rw [data_16_30207.1]; exact data_16_30207.2.2
  · rw [data_16_30207.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 30235). -/
theorem data_16_30235 : oddCount 30235 16 = 10 ∧
    acceleratedOrbit 16 30235 = 27244 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_30235 : ∀ j : Fin 16,
    30235 ≤ acceleratedOrbit j.val 30235 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_30235 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 30235) = 59049 * m + 27244 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 30235
  rw [data_16_30235.1, data_16_30235.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_30235 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 30235) < 65536 * m + 30235 := by
  apply descent_of_endpoint
  · rw [data_16_30235.1]; exact data_16_30235.2.2
  · rw [data_16_30235.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 30415). -/
theorem data_16_30415 : oddCount 30415 16 = 10 ∧
    acceleratedOrbit 16 30415 = 27406 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_30415 : ∀ j : Fin 16,
    30415 ≤ acceleratedOrbit j.val 30415 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_30415 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 30415) = 59049 * m + 27406 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 30415
  rw [data_16_30415.1, data_16_30415.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_30415 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 30415) < 65536 * m + 30415 := by
  apply descent_of_endpoint
  · rw [data_16_30415.1]; exact data_16_30415.2.2
  · rw [data_16_30415.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 30575). -/
theorem data_16_30575 : oddCount 30575 16 = 10 ∧
    acceleratedOrbit 16 30575 = 27550 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_30575 : ∀ j : Fin 16,
    30575 ≤ acceleratedOrbit j.val 30575 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_30575 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 30575) = 59049 * m + 27550 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 30575
  rw [data_16_30575.1, data_16_30575.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_30575 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 30575) < 65536 * m + 30575 := by
  apply descent_of_endpoint
  · rw [data_16_30575.1]; exact data_16_30575.2.2
  · rw [data_16_30575.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 30655). -/
theorem data_16_30655 : oddCount 30655 16 = 10 ∧
    acceleratedOrbit 16 30655 = 27622 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_30655 : ∀ j : Fin 16,
    30655 ≤ acceleratedOrbit j.val 30655 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_30655 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 30655) = 59049 * m + 27622 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 30655
  rw [data_16_30655.1, data_16_30655.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_30655 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 30655) < 65536 * m + 30655 := by
  apply descent_of_endpoint
  · rw [data_16_30655.1]; exact data_16_30655.2.2
  · rw [data_16_30655.2.1]; decide

end Collatz.Research.FirstDescent.Batch067
