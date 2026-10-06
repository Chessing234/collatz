import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 239. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch239
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 51263). -/
theorem data_20_51263 : oddCount 51263 20 = 12 ∧
    acceleratedOrbit 20 51263 = 25982 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_51263 : ∀ j : Fin 20,
    51263 ≤ acceleratedOrbit j.val 51263 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_51263 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 51263) = 531441 * m + 25982 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 51263
  rw [data_20_51263.1, data_20_51263.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_51263 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 51263) < 1048576 * m + 51263 := by
  apply descent_of_endpoint
  · rw [data_20_51263.1]; exact data_20_51263.2.2
  · rw [data_20_51263.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 51559). -/
theorem data_20_51559 : oddCount 51559 20 = 12 ∧
    acceleratedOrbit 20 51559 = 26132 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_51559 : ∀ j : Fin 20,
    51559 ≤ acceleratedOrbit j.val 51559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_51559 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 51559) = 531441 * m + 26132 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 51559
  rw [data_20_51559.1, data_20_51559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_51559 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 51559) < 1048576 * m + 51559 := by
  apply descent_of_endpoint
  · rw [data_20_51559.1]; exact data_20_51559.2.2
  · rw [data_20_51559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 51695). -/
theorem data_20_51695 : oddCount 51695 20 = 12 ∧
    acceleratedOrbit 20 51695 = 26201 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_51695 : ∀ j : Fin 20,
    51695 ≤ acceleratedOrbit j.val 51695 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_51695 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 51695) = 531441 * m + 26201 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 51695
  rw [data_20_51695.1, data_20_51695.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_51695 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 51695) < 1048576 * m + 51695 := by
  apply descent_of_endpoint
  · rw [data_20_51695.1]; exact data_20_51695.2.2
  · rw [data_20_51695.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 51995). -/
theorem data_20_51995 : oddCount 51995 20 = 12 ∧
    acceleratedOrbit 20 51995 = 26353 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_51995 : ∀ j : Fin 20,
    51995 ≤ acceleratedOrbit j.val 51995 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_51995 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 51995) = 531441 * m + 26353 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 51995
  rw [data_20_51995.1, data_20_51995.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_51995 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 51995) < 1048576 * m + 51995 := by
  apply descent_of_endpoint
  · rw [data_20_51995.1]; exact data_20_51995.2.2
  · rw [data_20_51995.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 52463). -/
theorem data_20_52463 : oddCount 52463 20 = 12 ∧
    acceleratedOrbit 20 52463 = 26590 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_52463 : ∀ j : Fin 20,
    52463 ≤ acceleratedOrbit j.val 52463 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_52463 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 52463) = 531441 * m + 26590 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 52463
  rw [data_20_52463.1, data_20_52463.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_52463 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 52463) < 1048576 * m + 52463 := by
  apply descent_of_endpoint
  · rw [data_20_52463.1]; exact data_20_52463.2.2
  · rw [data_20_52463.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 52583). -/
theorem data_20_52583 : oddCount 52583 20 = 12 ∧
    acceleratedOrbit 20 52583 = 26651 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_52583 : ∀ j : Fin 20,
    52583 ≤ acceleratedOrbit j.val 52583 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_52583 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 52583) = 531441 * m + 26651 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 52583
  rw [data_20_52583.1, data_20_52583.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_52583 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 52583) < 1048576 * m + 52583 := by
  apply descent_of_endpoint
  · rw [data_20_52583.1]; exact data_20_52583.2.2
  · rw [data_20_52583.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 53019). -/
theorem data_20_53019 : oddCount 53019 20 = 12 ∧
    acceleratedOrbit 20 53019 = 26872 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_53019 : ∀ j : Fin 20,
    53019 ≤ acceleratedOrbit j.val 53019 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_53019 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 53019) = 531441 * m + 26872 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 53019
  rw [data_20_53019.1, data_20_53019.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_53019 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 53019) < 1048576 * m + 53019 := by
  apply descent_of_endpoint
  · rw [data_20_53019.1]; exact data_20_53019.2.2
  · rw [data_20_53019.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 53575). -/
theorem data_20_53575 : oddCount 53575 20 = 12 ∧
    acceleratedOrbit 20 53575 = 27154 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_53575 : ∀ j : Fin 20,
    53575 ≤ acceleratedOrbit j.val 53575 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_53575 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 53575) = 531441 * m + 27154 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 53575
  rw [data_20_53575.1, data_20_53575.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_53575 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 53575) < 1048576 * m + 53575 := by
  apply descent_of_endpoint
  · rw [data_20_53575.1]; exact data_20_53575.2.2
  · rw [data_20_53575.2.1]; decide

end Collatz.Research.FirstDescent.Batch239
