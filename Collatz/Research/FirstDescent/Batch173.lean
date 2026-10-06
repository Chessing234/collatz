import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 173. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch173
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 157863). -/
theorem data_18_157863 : oddCount 157863 18 = 11 ∧
    acceleratedOrbit 18 157863 = 106679 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_157863 : ∀ j : Fin 18,
    157863 ≤ acceleratedOrbit j.val 157863 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_157863 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 157863) = 177147 * m + 106679 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 157863
  rw [data_18_157863.1, data_18_157863.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_157863 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 157863) < 262144 * m + 157863 := by
  apply descent_of_endpoint
  · rw [data_18_157863.1]; exact data_18_157863.2.2
  · rw [data_18_157863.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 157947). -/
theorem data_18_157947 : oddCount 157947 18 = 11 ∧
    acceleratedOrbit 18 157947 = 106736 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_157947 : ∀ j : Fin 18,
    157947 ≤ acceleratedOrbit j.val 157947 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_157947 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 157947) = 177147 * m + 106736 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 157947
  rw [data_18_157947.1, data_18_157947.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_157947 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 157947) < 262144 * m + 157947 := by
  apply descent_of_endpoint
  · rw [data_18_157947.1]; exact data_18_157947.2.2
  · rw [data_18_157947.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 158107). -/
theorem data_18_158107 : oddCount 158107 18 = 11 ∧
    acceleratedOrbit 18 158107 = 106844 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_158107 : ∀ j : Fin 18,
    158107 ≤ acceleratedOrbit j.val 158107 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_158107 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 158107) = 177147 * m + 106844 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 158107
  rw [data_18_158107.1, data_18_158107.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_158107 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 158107) < 262144 * m + 158107 := by
  apply descent_of_endpoint
  · rw [data_18_158107.1]; exact data_18_158107.2.2
  · rw [data_18_158107.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 158875). -/
theorem data_18_158875 : oddCount 158875 18 = 11 ∧
    acceleratedOrbit 18 158875 = 107363 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_158875 : ∀ j : Fin 18,
    158875 ≤ acceleratedOrbit j.val 158875 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_158875 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 158875) = 177147 * m + 107363 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 158875
  rw [data_18_158875.1, data_18_158875.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_158875 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 158875) < 262144 * m + 158875 := by
  apply descent_of_endpoint
  · rw [data_18_158875.1]; exact data_18_158875.2.2
  · rw [data_18_158875.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 158887). -/
theorem data_18_158887 : oddCount 158887 18 = 11 ∧
    acceleratedOrbit 18 158887 = 107371 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_158887 : ∀ j : Fin 18,
    158887 ≤ acceleratedOrbit j.val 158887 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_158887 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 158887) = 177147 * m + 107371 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 158887
  rw [data_18_158887.1, data_18_158887.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_158887 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 158887) < 262144 * m + 158887 := by
  apply descent_of_endpoint
  · rw [data_18_158887.1]; exact data_18_158887.2.2
  · rw [data_18_158887.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 159231). -/
theorem data_18_159231 : oddCount 159231 18 = 11 ∧
    acceleratedOrbit 18 159231 = 107603 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_159231 : ∀ j : Fin 18,
    159231 ≤ acceleratedOrbit j.val 159231 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_159231 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 159231) = 177147 * m + 107603 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 159231
  rw [data_18_159231.1, data_18_159231.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_159231 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 159231) < 262144 * m + 159231 := by
  apply descent_of_endpoint
  · rw [data_18_159231.1]; exact data_18_159231.2.2
  · rw [data_18_159231.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 159439). -/
theorem data_18_159439 : oddCount 159439 18 = 11 ∧
    acceleratedOrbit 18 159439 = 107744 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_159439 : ∀ j : Fin 18,
    159439 ≤ acceleratedOrbit j.val 159439 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_159439 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 159439) = 177147 * m + 107744 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 159439
  rw [data_18_159439.1, data_18_159439.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_159439 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 159439) < 262144 * m + 159439 := by
  apply descent_of_endpoint
  · rw [data_18_159439.1]; exact data_18_159439.2.2
  · rw [data_18_159439.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 159679). -/
theorem data_18_159679 : oddCount 159679 18 = 11 ∧
    acceleratedOrbit 18 159679 = 107906 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_159679 : ∀ j : Fin 18,
    159679 ≤ acceleratedOrbit j.val 159679 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_159679 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 159679) = 177147 * m + 107906 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 159679
  rw [data_18_159679.1, data_18_159679.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_159679 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 159679) < 262144 * m + 159679 := by
  apply descent_of_endpoint
  · rw [data_18_159679.1]; exact data_18_159679.2.2
  · rw [data_18_159679.2.1]; decide

end Collatz.Research.FirstDescent.Batch173
