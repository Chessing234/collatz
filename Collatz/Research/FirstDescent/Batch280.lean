import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 280. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch280
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 184923). -/
theorem data_20_184923 : oddCount 184923 20 = 12 ∧
    acceleratedOrbit 20 184923 = 93724 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_184923 : ∀ j : Fin 20,
    184923 ≤ acceleratedOrbit j.val 184923 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_184923 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 184923) = 531441 * m + 93724 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 184923
  rw [data_20_184923.1, data_20_184923.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_184923 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 184923) < 1048576 * m + 184923 := by
  apply descent_of_endpoint
  · rw [data_20_184923.1]; exact data_20_184923.2.2
  · rw [data_20_184923.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 185279). -/
theorem data_20_185279 : oddCount 185279 20 = 12 ∧
    acceleratedOrbit 20 185279 = 93904 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_185279 : ∀ j : Fin 20,
    185279 ≤ acceleratedOrbit j.val 185279 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_185279 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 185279) = 531441 * m + 93904 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 185279
  rw [data_20_185279.1, data_20_185279.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_185279 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 185279) < 1048576 * m + 185279 := by
  apply descent_of_endpoint
  · rw [data_20_185279.1]; exact data_20_185279.2.2
  · rw [data_20_185279.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 185671). -/
theorem data_20_185671 : oddCount 185671 20 = 12 ∧
    acceleratedOrbit 20 185671 = 94103 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_185671 : ∀ j : Fin 20,
    185671 ≤ acceleratedOrbit j.val 185671 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_185671 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 185671) = 531441 * m + 94103 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 185671
  rw [data_20_185671.1, data_20_185671.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_185671 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 185671) < 1048576 * m + 185671 := by
  apply descent_of_endpoint
  · rw [data_20_185671.1]; exact data_20_185671.2.2
  · rw [data_20_185671.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 185807). -/
theorem data_20_185807 : oddCount 185807 20 = 12 ∧
    acceleratedOrbit 20 185807 = 94172 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_185807 : ∀ j : Fin 20,
    185807 ≤ acceleratedOrbit j.val 185807 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_185807 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 185807) = 531441 * m + 94172 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 185807
  rw [data_20_185807.1, data_20_185807.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_185807 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 185807) < 1048576 * m + 185807 := by
  apply descent_of_endpoint
  · rw [data_20_185807.1]; exact data_20_185807.2.2
  · rw [data_20_185807.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 185959). -/
theorem data_20_185959 : oddCount 185959 20 = 12 ∧
    acceleratedOrbit 20 185959 = 94249 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_185959 : ∀ j : Fin 20,
    185959 ≤ acceleratedOrbit j.val 185959 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_185959 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 185959) = 531441 * m + 94249 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 185959
  rw [data_20_185959.1, data_20_185959.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_185959 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 185959) < 1048576 * m + 185959 := by
  apply descent_of_endpoint
  · rw [data_20_185959.1]; exact data_20_185959.2.2
  · rw [data_20_185959.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 186139). -/
theorem data_20_186139 : oddCount 186139 20 = 12 ∧
    acceleratedOrbit 20 186139 = 94340 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_186139 : ∀ j : Fin 20,
    186139 ≤ acceleratedOrbit j.val 186139 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_186139 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 186139) = 531441 * m + 94340 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 186139
  rw [data_20_186139.1, data_20_186139.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_186139 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 186139) < 1048576 * m + 186139 := by
  apply descent_of_endpoint
  · rw [data_20_186139.1]; exact data_20_186139.2.2
  · rw [data_20_186139.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 186535). -/
theorem data_20_186535 : oddCount 186535 20 = 12 ∧
    acceleratedOrbit 20 186535 = 94541 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_186535 : ∀ j : Fin 20,
    186535 ≤ acceleratedOrbit j.val 186535 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_186535 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 186535) = 531441 * m + 94541 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 186535
  rw [data_20_186535.1, data_20_186535.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_186535 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 186535) < 1048576 * m + 186535 := by
  apply descent_of_endpoint
  · rw [data_20_186535.1]; exact data_20_186535.2.2
  · rw [data_20_186535.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 186991). -/
theorem data_20_186991 : oddCount 186991 20 = 12 ∧
    acceleratedOrbit 20 186991 = 94772 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_186991 : ∀ j : Fin 20,
    186991 ≤ acceleratedOrbit j.val 186991 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_186991 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 186991) = 531441 * m + 94772 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 186991
  rw [data_20_186991.1, data_20_186991.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_186991 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 186991) < 1048576 * m + 186991 := by
  apply descent_of_endpoint
  · rw [data_20_186991.1]; exact data_20_186991.2.2
  · rw [data_20_186991.2.1]; decide

end Collatz.Research.FirstDescent.Batch280
