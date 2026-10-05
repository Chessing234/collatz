import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 272. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch272
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 156955). -/
theorem data_20_156955 : oddCount 156955 20 = 12 ∧
    acceleratedOrbit 20 156955 = 79549 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_156955 : ∀ j : Fin 20,
    156955 ≤ acceleratedOrbit j.val 156955 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_156955 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 156955) = 531441 * m + 79549 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 156955
  rw [data_20_156955.1, data_20_156955.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_156955 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 156955) < 1048576 * m + 156955 := by
  apply descent_of_endpoint
  · rw [data_20_156955.1]; exact data_20_156955.2.2
  · rw [data_20_156955.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 157767). -/
theorem data_20_157767 : oddCount 157767 20 = 12 ∧
    acceleratedOrbit 20 157767 = 79961 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_157767 : ∀ j : Fin 20,
    157767 ≤ acceleratedOrbit j.val 157767 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_157767 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 157767) = 531441 * m + 79961 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 157767
  rw [data_20_157767.1, data_20_157767.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_157767 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 157767) < 1048576 * m + 157767 := by
  apply descent_of_endpoint
  · rw [data_20_157767.1]; exact data_20_157767.2.2
  · rw [data_20_157767.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 157927). -/
theorem data_20_157927 : oddCount 157927 20 = 12 ∧
    acceleratedOrbit 20 157927 = 80042 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_157927 : ∀ j : Fin 20,
    157927 ≤ acceleratedOrbit j.val 157927 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_157927 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 157927) = 531441 * m + 80042 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 157927
  rw [data_20_157927.1, data_20_157927.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_157927 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 157927) < 1048576 * m + 157927 := by
  apply descent_of_endpoint
  · rw [data_20_157927.1]; exact data_20_157927.2.2
  · rw [data_20_157927.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 158567). -/
theorem data_20_158567 : oddCount 158567 20 = 12 ∧
    acceleratedOrbit 20 158567 = 80366 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_158567 : ∀ j : Fin 20,
    158567 ≤ acceleratedOrbit j.val 158567 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_158567 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 158567) = 531441 * m + 80366 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 158567
  rw [data_20_158567.1, data_20_158567.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_158567 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 158567) < 1048576 * m + 158567 := by
  apply descent_of_endpoint
  · rw [data_20_158567.1]; exact data_20_158567.2.2
  · rw [data_20_158567.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 158703). -/
theorem data_20_158703 : oddCount 158703 20 = 12 ∧
    acceleratedOrbit 20 158703 = 80435 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_158703 : ∀ j : Fin 20,
    158703 ≤ acceleratedOrbit j.val 158703 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_158703 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 158703) = 531441 * m + 80435 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 158703
  rw [data_20_158703.1, data_20_158703.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_158703 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 158703) < 1048576 * m + 158703 := by
  apply descent_of_endpoint
  · rw [data_20_158703.1]; exact data_20_158703.2.2
  · rw [data_20_158703.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 159003). -/
theorem data_20_159003 : oddCount 159003 20 = 12 ∧
    acceleratedOrbit 20 159003 = 80587 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_159003 : ∀ j : Fin 20,
    159003 ≤ acceleratedOrbit j.val 159003 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_159003 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 159003) = 531441 * m + 80587 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 159003
  rw [data_20_159003.1, data_20_159003.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_159003 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 159003) < 1048576 * m + 159003 := by
  apply descent_of_endpoint
  · rw [data_20_159003.1]; exact data_20_159003.2.2
  · rw [data_20_159003.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 159135). -/
theorem data_20_159135 : oddCount 159135 20 = 12 ∧
    acceleratedOrbit 20 159135 = 80654 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_159135 : ∀ j : Fin 20,
    159135 ≤ acceleratedOrbit j.val 159135 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_159135 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 159135) = 531441 * m + 80654 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 159135
  rw [data_20_159135.1, data_20_159135.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_159135 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 159135) < 1048576 * m + 159135 := by
  apply descent_of_endpoint
  · rw [data_20_159135.1]; exact data_20_159135.2.2
  · rw [data_20_159135.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 159259). -/
theorem data_20_159259 : oddCount 159259 20 = 12 ∧
    acceleratedOrbit 20 159259 = 80717 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_159259 : ∀ j : Fin 20,
    159259 ≤ acceleratedOrbit j.val 159259 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_159259 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 159259) = 531441 * m + 80717 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 159259
  rw [data_20_159259.1, data_20_159259.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_159259 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 159259) < 1048576 * m + 159259 := by
  apply descent_of_endpoint
  · rw [data_20_159259.1]; exact data_20_159259.2.2
  · rw [data_20_159259.2.1]; decide

end Collatz.Research.FirstDescent.Batch272
