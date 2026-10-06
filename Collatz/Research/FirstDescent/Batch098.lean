import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 98. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch098
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 64207). -/
theorem data_16_64207 : oddCount 64207 16 = 10 ∧
    acceleratedOrbit 16 64207 = 57853 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_64207 : ∀ j : Fin 16,
    64207 ≤ acceleratedOrbit j.val 64207 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_64207 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 64207) = 59049 * m + 57853 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 64207
  rw [data_16_64207.1, data_16_64207.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_64207 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 64207) < 65536 * m + 64207 := by
  apply descent_of_endpoint
  · rw [data_16_64207.1]; exact data_16_64207.2.2
  · rw [data_16_64207.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 64251). -/
theorem data_16_64251 : oddCount 64251 16 = 10 ∧
    acceleratedOrbit 16 64251 = 57893 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_64251 : ∀ j : Fin 16,
    64251 ≤ acceleratedOrbit j.val 64251 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_64251 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 64251) = 59049 * m + 57893 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 64251
  rw [data_16_64251.1, data_16_64251.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_64251 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 64251) < 65536 * m + 64251 := by
  apply descent_of_endpoint
  · rw [data_16_64251.1]; exact data_16_64251.2.2
  · rw [data_16_64251.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 64287). -/
theorem data_16_64287 : oddCount 64287 16 = 10 ∧
    acceleratedOrbit 16 64287 = 57925 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_64287 : ∀ j : Fin 16,
    64287 ≤ acceleratedOrbit j.val 64287 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_64287 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 64287) = 59049 * m + 57925 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 64287
  rw [data_16_64287.1, data_16_64287.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_64287 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 64287) < 65536 * m + 64287 := by
  apply descent_of_endpoint
  · rw [data_16_64287.1]; exact data_16_64287.2.2
  · rw [data_16_64287.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 64447). -/
theorem data_16_64447 : oddCount 64447 16 = 10 ∧
    acceleratedOrbit 16 64447 = 58069 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_64447 : ∀ j : Fin 16,
    64447 ≤ acceleratedOrbit j.val 64447 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_64447 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 64447) = 59049 * m + 58069 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 64447
  rw [data_16_64447.1, data_16_64447.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_64447 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 64447) < 65536 * m + 64447 := by
  apply descent_of_endpoint
  · rw [data_16_64447.1]; exact data_16_64447.2.2
  · rw [data_16_64447.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 64507). -/
theorem data_16_64507 : oddCount 64507 16 = 10 ∧
    acceleratedOrbit 16 64507 = 58124 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_64507 : ∀ j : Fin 16,
    64507 ≤ acceleratedOrbit j.val 64507 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_64507 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 64507) = 59049 * m + 58124 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 64507
  rw [data_16_64507.1, data_16_64507.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_64507 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 64507) < 65536 * m + 64507 := by
  apply descent_of_endpoint
  · rw [data_16_64507.1]; exact data_16_64507.2.2
  · rw [data_16_64507.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 64831). -/
theorem data_16_64831 : oddCount 64831 16 = 10 ∧
    acceleratedOrbit 16 64831 = 58415 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_64831 : ∀ j : Fin 16,
    64831 ≤ acceleratedOrbit j.val 64831 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_64831 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 64831) = 59049 * m + 58415 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 64831
  rw [data_16_64831.1, data_16_64831.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_64831 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 64831) < 65536 * m + 64831 := by
  apply descent_of_endpoint
  · rw [data_16_64831.1]; exact data_16_64831.2.2
  · rw [data_16_64831.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 64871). -/
theorem data_16_64871 : oddCount 64871 16 = 10 ∧
    acceleratedOrbit 16 64871 = 58451 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_64871 : ∀ j : Fin 16,
    64871 ≤ acceleratedOrbit j.val 64871 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_64871 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 64871) = 59049 * m + 58451 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 64871
  rw [data_16_64871.1, data_16_64871.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_64871 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 64871) < 65536 * m + 64871 := by
  apply descent_of_endpoint
  · rw [data_16_64871.1]; exact data_16_64871.2.2
  · rw [data_16_64871.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 65127). -/
theorem data_16_65127 : oddCount 65127 16 = 10 ∧
    acceleratedOrbit 16 65127 = 58682 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_65127 : ∀ j : Fin 16,
    65127 ≤ acceleratedOrbit j.val 65127 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_65127 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 65127) = 59049 * m + 58682 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 65127
  rw [data_16_65127.1, data_16_65127.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_65127 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 65127) < 65536 * m + 65127 := by
  apply descent_of_endpoint
  · rw [data_16_65127.1]; exact data_16_65127.2.2
  · rw [data_16_65127.2.1]; decide

end Collatz.Research.FirstDescent.Batch098
