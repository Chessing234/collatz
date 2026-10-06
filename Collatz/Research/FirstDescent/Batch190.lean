import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 190. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch190
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 195567). -/
theorem data_18_195567 : oddCount 195567 18 = 11 ∧
    acceleratedOrbit 18 195567 = 132158 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_195567 : ∀ j : Fin 18,
    195567 ≤ acceleratedOrbit j.val 195567 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_195567 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 195567) = 177147 * m + 132158 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 195567
  rw [data_18_195567.1, data_18_195567.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_195567 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 195567) < 262144 * m + 195567 := by
  apply descent_of_endpoint
  · rw [data_18_195567.1]; exact data_18_195567.2.2
  · rw [data_18_195567.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 196591). -/
theorem data_18_196591 : oddCount 196591 18 = 11 ∧
    acceleratedOrbit 18 196591 = 132850 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_196591 : ∀ j : Fin 18,
    196591 ≤ acceleratedOrbit j.val 196591 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_196591 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 196591) = 177147 * m + 132850 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 196591
  rw [data_18_196591.1, data_18_196591.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_196591 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 196591) < 262144 * m + 196591 := by
  apply descent_of_endpoint
  · rw [data_18_196591.1]; exact data_18_196591.2.2
  · rw [data_18_196591.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 196671). -/
theorem data_18_196671 : oddCount 196671 18 = 11 ∧
    acceleratedOrbit 18 196671 = 132904 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_196671 : ∀ j : Fin 18,
    196671 ≤ acceleratedOrbit j.val 196671 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_196671 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 196671) = 177147 * m + 132904 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 196671
  rw [data_18_196671.1, data_18_196671.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_196671 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 196671) < 262144 * m + 196671 := by
  apply descent_of_endpoint
  · rw [data_18_196671.1]; exact data_18_196671.2.2
  · rw [data_18_196671.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 196699). -/
theorem data_18_196699 : oddCount 196699 18 = 11 ∧
    acceleratedOrbit 18 196699 = 132923 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_196699 : ∀ j : Fin 18,
    196699 ≤ acceleratedOrbit j.val 196699 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_196699 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 196699) = 177147 * m + 132923 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 196699
  rw [data_18_196699.1, data_18_196699.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_196699 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 196699) < 262144 * m + 196699 := by
  apply descent_of_endpoint
  · rw [data_18_196699.1]; exact data_18_196699.2.2
  · rw [data_18_196699.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 196711). -/
theorem data_18_196711 : oddCount 196711 18 = 11 ∧
    acceleratedOrbit 18 196711 = 132931 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_196711 : ∀ j : Fin 18,
    196711 ≤ acceleratedOrbit j.val 196711 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_196711 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 196711) = 177147 * m + 132931 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 196711
  rw [data_18_196711.1, data_18_196711.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_196711 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 196711) < 262144 * m + 196711 := by
  apply descent_of_endpoint
  · rw [data_18_196711.1]; exact data_18_196711.2.2
  · rw [data_18_196711.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 197503). -/
theorem data_18_197503 : oddCount 197503 18 = 11 ∧
    acceleratedOrbit 18 197503 = 133466 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_197503 : ∀ j : Fin 18,
    197503 ≤ acceleratedOrbit j.val 197503 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_197503 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 197503) = 177147 * m + 133466 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 197503
  rw [data_18_197503.1, data_18_197503.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_197503 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 197503) < 262144 * m + 197503 := by
  apply descent_of_endpoint
  · rw [data_18_197503.1]; exact data_18_197503.2.2
  · rw [data_18_197503.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 197599). -/
theorem data_18_197599 : oddCount 197599 18 = 11 ∧
    acceleratedOrbit 18 197599 = 133531 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_197599 : ∀ j : Fin 18,
    197599 ≤ acceleratedOrbit j.val 197599 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_197599 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 197599) = 177147 * m + 133531 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 197599
  rw [data_18_197599.1, data_18_197599.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_197599 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 197599) < 262144 * m + 197599 := by
  apply descent_of_endpoint
  · rw [data_18_197599.1]; exact data_18_197599.2.2
  · rw [data_18_197599.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 197723). -/
theorem data_18_197723 : oddCount 197723 18 = 11 ∧
    acceleratedOrbit 18 197723 = 133615 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_197723 : ∀ j : Fin 18,
    197723 ≤ acceleratedOrbit j.val 197723 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_197723 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 197723) = 177147 * m + 133615 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 197723
  rw [data_18_197723.1, data_18_197723.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_197723 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 197723) < 262144 * m + 197723 := by
  apply descent_of_endpoint
  · rw [data_18_197723.1]; exact data_18_197723.2.2
  · rw [data_18_197723.2.1]; decide

end Collatz.Research.FirstDescent.Batch190
