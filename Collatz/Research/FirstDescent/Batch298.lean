import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 298. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch298
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 234011). -/
theorem data_20_234011 : oddCount 234011 20 = 12 ∧
    acceleratedOrbit 20 234011 = 118603 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_234011 : ∀ j : Fin 20,
    234011 ≤ acceleratedOrbit j.val 234011 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_234011 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 234011) = 531441 * m + 118603 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 234011
  rw [data_20_234011.1, data_20_234011.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_234011 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 234011) < 1048576 * m + 234011 := by
  apply descent_of_endpoint
  · rw [data_20_234011.1]; exact data_20_234011.2.2
  · rw [data_20_234011.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 234367). -/
theorem data_20_234367 : oddCount 234367 20 = 12 ∧
    acceleratedOrbit 20 234367 = 118783 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_234367 : ∀ j : Fin 20,
    234367 ≤ acceleratedOrbit j.val 234367 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_234367 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 234367) = 531441 * m + 118783 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 234367
  rw [data_20_234367.1, data_20_234367.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_234367 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 234367) < 1048576 * m + 234367 := by
  apply descent_of_endpoint
  · rw [data_20_234367.1]; exact data_20_234367.2.2
  · rw [data_20_234367.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 234463). -/
theorem data_20_234463 : oddCount 234463 20 = 12 ∧
    acceleratedOrbit 20 234463 = 118832 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_234463 : ∀ j : Fin 20,
    234463 ≤ acceleratedOrbit j.val 234463 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_234463 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 234463) = 531441 * m + 118832 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 234463
  rw [data_20_234463.1, data_20_234463.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_234463 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 234463) < 1048576 * m + 234463 := by
  apply descent_of_endpoint
  · rw [data_20_234463.1]; exact data_20_234463.2.2
  · rw [data_20_234463.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 235375). -/
theorem data_20_235375 : oddCount 235375 20 = 12 ∧
    acceleratedOrbit 20 235375 = 119294 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_235375 : ∀ j : Fin 20,
    235375 ≤ acceleratedOrbit j.val 235375 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_235375 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 235375) = 531441 * m + 119294 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 235375
  rw [data_20_235375.1, data_20_235375.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_235375 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 235375) < 1048576 * m + 235375 := by
  apply descent_of_endpoint
  · rw [data_20_235375.1]; exact data_20_235375.2.2
  · rw [data_20_235375.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 235391). -/
theorem data_20_235391 : oddCount 235391 20 = 12 ∧
    acceleratedOrbit 20 235391 = 119302 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_235391 : ∀ j : Fin 20,
    235391 ≤ acceleratedOrbit j.val 235391 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_235391 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 235391) = 531441 * m + 119302 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 235391
  rw [data_20_235391.1, data_20_235391.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_235391 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 235391) < 1048576 * m + 235391 := by
  apply descent_of_endpoint
  · rw [data_20_235391.1]; exact data_20_235391.2.2
  · rw [data_20_235391.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 235487). -/
theorem data_20_235487 : oddCount 235487 20 = 12 ∧
    acceleratedOrbit 20 235487 = 119351 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_235487 : ∀ j : Fin 20,
    235487 ≤ acceleratedOrbit j.val 235487 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_235487 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 235487) = 531441 * m + 119351 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 235487
  rw [data_20_235487.1, data_20_235487.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_235487 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 235487) < 1048576 * m + 235487 := by
  apply descent_of_endpoint
  · rw [data_20_235487.1]; exact data_20_235487.2.2
  · rw [data_20_235487.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 236079). -/
theorem data_20_236079 : oddCount 236079 20 = 12 ∧
    acceleratedOrbit 20 236079 = 119651 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_236079 : ∀ j : Fin 20,
    236079 ≤ acceleratedOrbit j.val 236079 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_236079 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 236079) = 531441 * m + 119651 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 236079
  rw [data_20_236079.1, data_20_236079.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_236079 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 236079) < 1048576 * m + 236079 := by
  apply descent_of_endpoint
  · rw [data_20_236079.1]; exact data_20_236079.2.2
  · rw [data_20_236079.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 236239). -/
theorem data_20_236239 : oddCount 236239 20 = 12 ∧
    acceleratedOrbit 20 236239 = 119732 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_236239 : ∀ j : Fin 20,
    236239 ≤ acceleratedOrbit j.val 236239 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_236239 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 236239) = 531441 * m + 119732 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 236239
  rw [data_20_236239.1, data_20_236239.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_236239 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 236239) < 1048576 * m + 236239 := by
  apply descent_of_endpoint
  · rw [data_20_236239.1]; exact data_20_236239.2.2
  · rw [data_20_236239.2.1]; decide

end Collatz.Research.FirstDescent.Batch298
