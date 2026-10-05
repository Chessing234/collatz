import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 95. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch095
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 60911). -/
theorem data_16_60911 : oddCount 60911 16 = 10 ∧
    acceleratedOrbit 16 60911 = 54883 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_60911 : ∀ j : Fin 16,
    60911 ≤ acceleratedOrbit j.val 60911 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_60911 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 60911) = 59049 * m + 54883 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 60911
  rw [data_16_60911.1, data_16_60911.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_60911 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 60911) < 65536 * m + 60911 := by
  apply descent_of_endpoint
  · rw [data_16_60911.1]; exact data_16_60911.2.2
  · rw [data_16_60911.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 60955). -/
theorem data_16_60955 : oddCount 60955 16 = 10 ∧
    acceleratedOrbit 16 60955 = 54923 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_60955 : ∀ j : Fin 16,
    60955 ≤ acceleratedOrbit j.val 60955 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_60955 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 60955) = 59049 * m + 54923 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 60955
  rw [data_16_60955.1, data_16_60955.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_60955 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 60955) < 65536 * m + 60955 := by
  apply descent_of_endpoint
  · rw [data_16_60955.1]; exact data_16_60955.2.2
  · rw [data_16_60955.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 61135). -/
theorem data_16_61135 : oddCount 61135 16 = 10 ∧
    acceleratedOrbit 16 61135 = 55085 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_61135 : ∀ j : Fin 16,
    61135 ≤ acceleratedOrbit j.val 61135 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_61135 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 61135) = 59049 * m + 55085 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 61135
  rw [data_16_61135.1, data_16_61135.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_61135 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 61135) < 65536 * m + 61135 := by
  apply descent_of_endpoint
  · rw [data_16_61135.1]; exact data_16_61135.2.2
  · rw [data_16_61135.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 61351). -/
theorem data_16_61351 : oddCount 61351 16 = 10 ∧
    acceleratedOrbit 16 61351 = 55280 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_61351 : ∀ j : Fin 16,
    61351 ≤ acceleratedOrbit j.val 61351 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_61351 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 61351) = 59049 * m + 55280 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 61351
  rw [data_16_61351.1, data_16_61351.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_61351 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 61351) < 65536 * m + 61351 := by
  apply descent_of_endpoint
  · rw [data_16_61351.1]; exact data_16_61351.2.2
  · rw [data_16_61351.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 61375). -/
theorem data_16_61375 : oddCount 61375 16 = 10 ∧
    acceleratedOrbit 16 61375 = 55301 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_61375 : ∀ j : Fin 16,
    61375 ≤ acceleratedOrbit j.val 61375 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_61375 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 61375) = 59049 * m + 55301 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 61375
  rw [data_16_61375.1, data_16_61375.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_61375 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 61375) < 65536 * m + 61375 := by
  apply descent_of_endpoint
  · rw [data_16_61375.1]; exact data_16_61375.2.2
  · rw [data_16_61375.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 61531). -/
theorem data_16_61531 : oddCount 61531 16 = 10 ∧
    acceleratedOrbit 16 61531 = 55442 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_61531 : ∀ j : Fin 16,
    61531 ≤ acceleratedOrbit j.val 61531 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_61531 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 61531) = 59049 * m + 55442 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 61531
  rw [data_16_61531.1, data_16_61531.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_61531 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 61531) < 65536 * m + 61531 := by
  apply descent_of_endpoint
  · rw [data_16_61531.1]; exact data_16_61531.2.2
  · rw [data_16_61531.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 61631). -/
theorem data_16_61631 : oddCount 61631 16 = 10 ∧
    acceleratedOrbit 16 61631 = 55532 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_61631 : ∀ j : Fin 16,
    61631 ≤ acceleratedOrbit j.val 61631 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_61631 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 61631) = 59049 * m + 55532 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 61631
  rw [data_16_61631.1, data_16_61631.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_61631 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 61631) < 65536 * m + 61631 := by
  apply descent_of_endpoint
  · rw [data_16_61631.1]; exact data_16_61631.2.2
  · rw [data_16_61631.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 61663). -/
theorem data_16_61663 : oddCount 61663 16 = 10 ∧
    acceleratedOrbit 16 61663 = 55561 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_61663 : ∀ j : Fin 16,
    61663 ≤ acceleratedOrbit j.val 61663 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_61663 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 61663) = 59049 * m + 55561 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 61663
  rw [data_16_61663.1, data_16_61663.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_61663 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 61663) < 65536 * m + 61663 := by
  apply descent_of_endpoint
  · rw [data_16_61663.1]; exact data_16_61663.2.2
  · rw [data_16_61663.2.1]; decide

end Collatz.Research.FirstDescent.Batch095
