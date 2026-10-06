import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 81. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch081
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 45103). -/
theorem data_16_45103 : oddCount 45103 16 = 10 ∧
    acceleratedOrbit 16 45103 = 40640 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_45103 : ∀ j : Fin 16,
    45103 ≤ acceleratedOrbit j.val 45103 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_45103 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 45103) = 59049 * m + 40640 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 45103
  rw [data_16_45103.1, data_16_45103.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_45103 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 45103) < 65536 * m + 45103 := by
  apply descent_of_endpoint
  · rw [data_16_45103.1]; exact data_16_45103.2.2
  · rw [data_16_45103.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 45223). -/
theorem data_16_45223 : oddCount 45223 16 = 10 ∧
    acceleratedOrbit 16 45223 = 40748 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_45223 : ∀ j : Fin 16,
    45223 ≤ acceleratedOrbit j.val 45223 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_45223 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 45223) = 59049 * m + 40748 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 45223
  rw [data_16_45223.1, data_16_45223.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_45223 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 45223) < 65536 * m + 45223 := by
  apply descent_of_endpoint
  · rw [data_16_45223.1]; exact data_16_45223.2.2
  · rw [data_16_45223.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 45359). -/
theorem data_16_45359 : oddCount 45359 16 = 10 ∧
    acceleratedOrbit 16 45359 = 40871 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_45359 : ∀ j : Fin 16,
    45359 ≤ acceleratedOrbit j.val 45359 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_45359 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 45359) = 59049 * m + 40871 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 45359
  rw [data_16_45359.1, data_16_45359.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_45359 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 45359) < 65536 * m + 45359 := by
  apply descent_of_endpoint
  · rw [data_16_45359.1]; exact data_16_45359.2.2
  · rw [data_16_45359.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 45503). -/
theorem data_16_45503 : oddCount 45503 16 = 10 ∧
    acceleratedOrbit 16 45503 = 41000 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_45503 : ∀ j : Fin 16,
    45503 ≤ acceleratedOrbit j.val 45503 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_45503 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 45503) = 59049 * m + 41000 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 45503
  rw [data_16_45503.1, data_16_45503.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_45503 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 45503) < 65536 * m + 45503 := by
  apply descent_of_endpoint
  · rw [data_16_45503.1]; exact data_16_45503.2.2
  · rw [data_16_45503.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 45535). -/
theorem data_16_45535 : oddCount 45535 16 = 10 ∧
    acceleratedOrbit 16 45535 = 41029 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_45535 : ∀ j : Fin 16,
    45535 ≤ acceleratedOrbit j.val 45535 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_45535 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 45535) = 59049 * m + 41029 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 45535
  rw [data_16_45535.1, data_16_45535.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_45535 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 45535) < 65536 * m + 45535 := by
  apply descent_of_endpoint
  · rw [data_16_45535.1]; exact data_16_45535.2.2
  · rw [data_16_45535.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 45599). -/
theorem data_16_45599 : oddCount 45599 16 = 10 ∧
    acceleratedOrbit 16 45599 = 41087 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_45599 : ∀ j : Fin 16,
    45599 ≤ acceleratedOrbit j.val 45599 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_45599 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 45599) = 59049 * m + 41087 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 45599
  rw [data_16_45599.1, data_16_45599.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_45599 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 45599) < 65536 * m + 45599 := by
  apply descent_of_endpoint
  · rw [data_16_45599.1]; exact data_16_45599.2.2
  · rw [data_16_45599.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 45679). -/
theorem data_16_45679 : oddCount 45679 16 = 10 ∧
    acceleratedOrbit 16 45679 = 41159 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_45679 : ∀ j : Fin 16,
    45679 ≤ acceleratedOrbit j.val 45679 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_45679 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 45679) = 59049 * m + 41159 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 45679
  rw [data_16_45679.1, data_16_45679.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_45679 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 45679) < 65536 * m + 45679 := by
  apply descent_of_endpoint
  · rw [data_16_45679.1]; exact data_16_45679.2.2
  · rw [data_16_45679.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 45799). -/
theorem data_16_45799 : oddCount 45799 16 = 10 ∧
    acceleratedOrbit 16 45799 = 41267 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_45799 : ∀ j : Fin 16,
    45799 ≤ acceleratedOrbit j.val 45799 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_45799 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 45799) = 59049 * m + 41267 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 45799
  rw [data_16_45799.1, data_16_45799.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_45799 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 45799) < 65536 * m + 45799 := by
  apply descent_of_endpoint
  · rw [data_16_45799.1]; exact data_16_45799.2.2
  · rw [data_16_45799.2.1]; decide

end Collatz.Research.FirstDescent.Batch081
