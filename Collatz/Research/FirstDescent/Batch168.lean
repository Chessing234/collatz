import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 168. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch168
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 147047). -/
theorem data_18_147047 : oddCount 147047 18 = 11 ∧
    acceleratedOrbit 18 147047 = 99370 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_147047 : ∀ j : Fin 18,
    147047 ≤ acceleratedOrbit j.val 147047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_147047 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 147047) = 177147 * m + 99370 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 147047
  rw [data_18_147047.1, data_18_147047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_147047 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 147047) < 262144 * m + 147047 := by
  apply descent_of_endpoint
  · rw [data_18_147047.1]; exact data_18_147047.2.2
  · rw [data_18_147047.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 147327). -/
theorem data_18_147327 : oddCount 147327 18 = 11 ∧
    acceleratedOrbit 18 147327 = 99559 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_147327 : ∀ j : Fin 18,
    147327 ≤ acceleratedOrbit j.val 147327 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_147327 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 147327) = 177147 * m + 99559 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 147327
  rw [data_18_147327.1, data_18_147327.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_147327 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 147327) < 262144 * m + 147327 := by
  apply descent_of_endpoint
  · rw [data_18_147327.1]; exact data_18_147327.2.2
  · rw [data_18_147327.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 147439). -/
theorem data_18_147439 : oddCount 147439 18 = 11 ∧
    acceleratedOrbit 18 147439 = 99635 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_147439 : ∀ j : Fin 18,
    147439 ≤ acceleratedOrbit j.val 147439 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_147439 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 147439) = 177147 * m + 99635 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 147439
  rw [data_18_147439.1, data_18_147439.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_147439 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 147439) < 262144 * m + 147439 := by
  apply descent_of_endpoint
  · rw [data_18_147439.1]; exact data_18_147439.2.2
  · rw [data_18_147439.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 147519). -/
theorem data_18_147519 : oddCount 147519 18 = 11 ∧
    acceleratedOrbit 18 147519 = 99689 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_147519 : ∀ j : Fin 18,
    147519 ≤ acceleratedOrbit j.val 147519 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_147519 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 147519) = 177147 * m + 99689 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 147519
  rw [data_18_147519.1, data_18_147519.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_147519 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 147519) < 262144 * m + 147519 := by
  apply descent_of_endpoint
  · rw [data_18_147519.1]; exact data_18_147519.2.2
  · rw [data_18_147519.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 147559). -/
theorem data_18_147559 : oddCount 147559 18 = 11 ∧
    acceleratedOrbit 18 147559 = 99716 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_147559 : ∀ j : Fin 18,
    147559 ≤ acceleratedOrbit j.val 147559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_147559 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 147559) = 177147 * m + 99716 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 147559
  rw [data_18_147559.1, data_18_147559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_147559 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 147559) < 262144 * m + 147559 := by
  apply descent_of_endpoint
  · rw [data_18_147559.1]; exact data_18_147559.2.2
  · rw [data_18_147559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 147679). -/
theorem data_18_147679 : oddCount 147679 18 = 11 ∧
    acceleratedOrbit 18 147679 = 99797 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_147679 : ∀ j : Fin 18,
    147679 ≤ acceleratedOrbit j.val 147679 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_147679 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 147679) = 177147 * m + 99797 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 147679
  rw [data_18_147679.1, data_18_147679.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_147679 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 147679) < 262144 * m + 147679 := by
  apply descent_of_endpoint
  · rw [data_18_147679.1]; exact data_18_147679.2.2
  · rw [data_18_147679.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 148015). -/
theorem data_18_148015 : oddCount 148015 18 = 11 ∧
    acceleratedOrbit 18 148015 = 100024 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_148015 : ∀ j : Fin 18,
    148015 ≤ acceleratedOrbit j.val 148015 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_148015 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 148015) = 177147 * m + 100024 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 148015
  rw [data_18_148015.1, data_18_148015.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_148015 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 148015) < 262144 * m + 148015 := by
  apply descent_of_endpoint
  · rw [data_18_148015.1]; exact data_18_148015.2.2
  · rw [data_18_148015.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 148059). -/
theorem data_18_148059 : oddCount 148059 18 = 11 ∧
    acceleratedOrbit 18 148059 = 100054 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_148059 : ∀ j : Fin 18,
    148059 ≤ acceleratedOrbit j.val 148059 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_148059 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 148059) = 177147 * m + 100054 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 148059
  rw [data_18_148059.1, data_18_148059.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_148059 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 148059) < 262144 * m + 148059 := by
  apply descent_of_endpoint
  · rw [data_18_148059.1]; exact data_18_148059.2.2
  · rw [data_18_148059.2.1]; decide

end Collatz.Research.FirstDescent.Batch168
