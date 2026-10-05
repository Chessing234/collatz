import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 200. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch200
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 217807). -/
theorem data_18_217807 : oddCount 217807 18 = 11 ∧
    acceleratedOrbit 18 217807 = 147187 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_217807 : ∀ j : Fin 18,
    217807 ≤ acceleratedOrbit j.val 217807 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_217807 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 217807) = 177147 * m + 147187 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 217807
  rw [data_18_217807.1, data_18_217807.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_217807 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 217807) < 262144 * m + 217807 := by
  apply descent_of_endpoint
  · rw [data_18_217807.1]; exact data_18_217807.2.2
  · rw [data_18_217807.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 217887). -/
theorem data_18_217887 : oddCount 217887 18 = 11 ∧
    acceleratedOrbit 18 217887 = 147241 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_217887 : ∀ j : Fin 18,
    217887 ≤ acceleratedOrbit j.val 217887 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_217887 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 217887) = 177147 * m + 147241 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 217887
  rw [data_18_217887.1, data_18_217887.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_217887 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 217887) < 262144 * m + 217887 := by
  apply descent_of_endpoint
  · rw [data_18_217887.1]; exact data_18_217887.2.2
  · rw [data_18_217887.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 218159). -/
theorem data_18_218159 : oddCount 218159 18 = 11 ∧
    acceleratedOrbit 18 218159 = 147425 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_218159 : ∀ j : Fin 18,
    218159 ≤ acceleratedOrbit j.val 218159 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_218159 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 218159) = 177147 * m + 147425 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 218159
  rw [data_18_218159.1, data_18_218159.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_218159 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 218159) < 262144 * m + 218159 := by
  apply descent_of_endpoint
  · rw [data_18_218159.1]; exact data_18_218159.2.2
  · rw [data_18_218159.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 218279). -/
theorem data_18_218279 : oddCount 218279 18 = 11 ∧
    acceleratedOrbit 18 218279 = 147506 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_218279 : ∀ j : Fin 18,
    218279 ≤ acceleratedOrbit j.val 218279 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_218279 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 218279) = 177147 * m + 147506 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 218279
  rw [data_18_218279.1, data_18_218279.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_218279 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 218279) < 262144 * m + 218279 := by
  apply descent_of_endpoint
  · rw [data_18_218279.1]; exact data_18_218279.2.2
  · rw [data_18_218279.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 218367). -/
theorem data_18_218367 : oddCount 218367 18 = 11 ∧
    acceleratedOrbit 18 218367 = 147565 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_218367 : ∀ j : Fin 18,
    218367 ≤ acceleratedOrbit j.val 218367 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_218367 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 218367) = 177147 * m + 147565 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 218367
  rw [data_18_218367.1, data_18_218367.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_218367 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 218367) < 262144 * m + 218367 := by
  apply descent_of_endpoint
  · rw [data_18_218367.1]; exact data_18_218367.2.2
  · rw [data_18_218367.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 218439). -/
theorem data_18_218439 : oddCount 218439 18 = 11 ∧
    acceleratedOrbit 18 218439 = 147614 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_218439 : ∀ j : Fin 18,
    218439 ≤ acceleratedOrbit j.val 218439 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_218439 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 218439) = 177147 * m + 147614 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 218439
  rw [data_18_218439.1, data_18_218439.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_218439 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 218439) < 262144 * m + 218439 := by
  apply descent_of_endpoint
  · rw [data_18_218439.1]; exact data_18_218439.2.2
  · rw [data_18_218439.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 218575). -/
theorem data_18_218575 : oddCount 218575 18 = 11 ∧
    acceleratedOrbit 18 218575 = 147706 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_218575 : ∀ j : Fin 18,
    218575 ≤ acceleratedOrbit j.val 218575 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_218575 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 218575) = 177147 * m + 147706 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 218575
  rw [data_18_218575.1, data_18_218575.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_218575 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 218575) < 262144 * m + 218575 := by
  apply descent_of_endpoint
  · rw [data_18_218575.1]; exact data_18_218575.2.2
  · rw [data_18_218575.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 218855). -/
theorem data_18_218855 : oddCount 218855 18 = 11 ∧
    acceleratedOrbit 18 218855 = 147895 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_218855 : ∀ j : Fin 18,
    218855 ≤ acceleratedOrbit j.val 218855 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_218855 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 218855) = 177147 * m + 147895 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 218855
  rw [data_18_218855.1, data_18_218855.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_218855 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 218855) < 262144 * m + 218855 := by
  apply descent_of_endpoint
  · rw [data_18_218855.1]; exact data_18_218855.2.2
  · rw [data_18_218855.2.1]; decide

end Collatz.Research.FirstDescent.Batch200
