import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 187. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch187
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 187375). -/
theorem data_18_187375 : oddCount 187375 18 = 11 ∧
    acceleratedOrbit 18 187375 = 126622 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_187375 : ∀ j : Fin 18,
    187375 ≤ acceleratedOrbit j.val 187375 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_187375 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 187375) = 177147 * m + 126622 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 187375
  rw [data_18_187375.1, data_18_187375.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_187375 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 187375) < 262144 * m + 187375 := by
  apply descent_of_endpoint
  · rw [data_18_187375.1]; exact data_18_187375.2.2
  · rw [data_18_187375.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 187495). -/
theorem data_18_187495 : oddCount 187495 18 = 11 ∧
    acceleratedOrbit 18 187495 = 126703 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_187495 : ∀ j : Fin 18,
    187495 ≤ acceleratedOrbit j.val 187495 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_187495 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 187495) = 177147 * m + 126703 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 187495
  rw [data_18_187495.1, data_18_187495.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_187495 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 187495) < 262144 * m + 187495 := by
  apply descent_of_endpoint
  · rw [data_18_187495.1]; exact data_18_187495.2.2
  · rw [data_18_187495.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 187519). -/
theorem data_18_187519 : oddCount 187519 18 = 11 ∧
    acceleratedOrbit 18 187519 = 126719 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_187519 : ∀ j : Fin 18,
    187519 ≤ acceleratedOrbit j.val 187519 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_187519 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 187519) = 177147 * m + 126719 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 187519
  rw [data_18_187519.1, data_18_187519.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_187519 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 187519) < 262144 * m + 187519 := by
  apply descent_of_endpoint
  · rw [data_18_187519.1]; exact data_18_187519.2.2
  · rw [data_18_187519.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 187887). -/
theorem data_18_187887 : oddCount 187887 18 = 11 ∧
    acceleratedOrbit 18 187887 = 126968 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_187887 : ∀ j : Fin 18,
    187887 ≤ acceleratedOrbit j.val 187887 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_187887 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 187887) = 177147 * m + 126968 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 187887
  rw [data_18_187887.1, data_18_187887.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_187887 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 187887) < 262144 * m + 187887 := by
  apply descent_of_endpoint
  · rw [data_18_187887.1]; exact data_18_187887.2.2
  · rw [data_18_187887.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 188655). -/
theorem data_18_188655 : oddCount 188655 18 = 11 ∧
    acceleratedOrbit 18 188655 = 127487 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_188655 : ∀ j : Fin 18,
    188655 ≤ acceleratedOrbit j.val 188655 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_188655 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 188655) = 177147 * m + 127487 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 188655
  rw [data_18_188655.1, data_18_188655.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_188655 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 188655) < 262144 * m + 188655 := by
  apply descent_of_endpoint
  · rw [data_18_188655.1]; exact data_18_188655.2.2
  · rw [data_18_188655.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 189511). -/
theorem data_18_189511 : oddCount 189511 18 = 11 ∧
    acceleratedOrbit 18 189511 = 128066 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_189511 : ∀ j : Fin 18,
    189511 ≤ acceleratedOrbit j.val 189511 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_189511 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 189511) = 177147 * m + 128066 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 189511
  rw [data_18_189511.1, data_18_189511.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_189511 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 189511) < 262144 * m + 189511 := by
  apply descent_of_endpoint
  · rw [data_18_189511.1]; exact data_18_189511.2.2
  · rw [data_18_189511.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 189759). -/
theorem data_18_189759 : oddCount 189759 18 = 11 ∧
    acceleratedOrbit 18 189759 = 128233 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_189759 : ∀ j : Fin 18,
    189759 ≤ acceleratedOrbit j.val 189759 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_189759 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 189759) = 177147 * m + 128233 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 189759
  rw [data_18_189759.1, data_18_189759.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_189759 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 189759) < 262144 * m + 189759 := by
  apply descent_of_endpoint
  · rw [data_18_189759.1]; exact data_18_189759.2.2
  · rw [data_18_189759.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 189799). -/
theorem data_18_189799 : oddCount 189799 18 = 11 ∧
    acceleratedOrbit 18 189799 = 128260 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_189799 : ∀ j : Fin 18,
    189799 ≤ acceleratedOrbit j.val 189799 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_189799 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 189799) = 177147 * m + 128260 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 189799
  rw [data_18_189799.1, data_18_189799.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_189799 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 189799) < 262144 * m + 189799 := by
  apply descent_of_endpoint
  · rw [data_18_189799.1]; exact data_18_189799.2.2
  · rw [data_18_189799.2.1]; decide

end Collatz.Research.FirstDescent.Batch187
