import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 197. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch197
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 211663). -/
theorem data_18_211663 : oddCount 211663 18 = 11 ∧
    acceleratedOrbit 18 211663 = 143035 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_211663 : ∀ j : Fin 18,
    211663 ≤ acceleratedOrbit j.val 211663 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_211663 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 211663) = 177147 * m + 143035 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 211663
  rw [data_18_211663.1, data_18_211663.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_211663 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 211663) < 262144 * m + 211663 := by
  apply descent_of_endpoint
  · rw [data_18_211663.1]; exact data_18_211663.2.2
  · rw [data_18_211663.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 211707). -/
theorem data_18_211707 : oddCount 211707 18 = 11 ∧
    acceleratedOrbit 18 211707 = 143065 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_211707 : ∀ j : Fin 18,
    211707 ≤ acceleratedOrbit j.val 211707 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_211707 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 211707) = 177147 * m + 143065 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 211707
  rw [data_18_211707.1, data_18_211707.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_211707 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 211707) < 262144 * m + 211707 := by
  apply descent_of_endpoint
  · rw [data_18_211707.1]; exact data_18_211707.2.2
  · rw [data_18_211707.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 211743). -/
theorem data_18_211743 : oddCount 211743 18 = 11 ∧
    acceleratedOrbit 18 211743 = 143089 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_211743 : ∀ j : Fin 18,
    211743 ≤ acceleratedOrbit j.val 211743 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_211743 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 211743) = 177147 * m + 143089 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 211743
  rw [data_18_211743.1, data_18_211743.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_211743 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 211743) < 262144 * m + 211743 := by
  apply descent_of_endpoint
  · rw [data_18_211743.1]; exact data_18_211743.2.2
  · rw [data_18_211743.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 211935). -/
theorem data_18_211935 : oddCount 211935 18 = 11 ∧
    acceleratedOrbit 18 211935 = 143219 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_211935 : ∀ j : Fin 18,
    211935 ≤ acceleratedOrbit j.val 211935 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_211935 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 211935) = 177147 * m + 143219 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 211935
  rw [data_18_211935.1, data_18_211935.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_211935 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 211935) < 262144 * m + 211935 := by
  apply descent_of_endpoint
  · rw [data_18_211935.1]; exact data_18_211935.2.2
  · rw [data_18_211935.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 212135). -/
theorem data_18_212135 : oddCount 212135 18 = 11 ∧
    acceleratedOrbit 18 212135 = 143354 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_212135 : ∀ j : Fin 18,
    212135 ≤ acceleratedOrbit j.val 212135 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_212135 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 212135) = 177147 * m + 143354 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 212135
  rw [data_18_212135.1, data_18_212135.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_212135 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 212135) < 262144 * m + 212135 := by
  apply descent_of_endpoint
  · rw [data_18_212135.1]; exact data_18_212135.2.2
  · rw [data_18_212135.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 212219). -/
theorem data_18_212219 : oddCount 212219 18 = 11 ∧
    acceleratedOrbit 18 212219 = 143411 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_212219 : ∀ j : Fin 18,
    212219 ≤ acceleratedOrbit j.val 212219 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_212219 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 212219) = 177147 * m + 143411 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 212219
  rw [data_18_212219.1, data_18_212219.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_212219 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 212219) < 262144 * m + 212219 := by
  apply descent_of_endpoint
  · rw [data_18_212219.1]; exact data_18_212219.2.2
  · rw [data_18_212219.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 212223). -/
theorem data_18_212223 : oddCount 212223 18 = 11 ∧
    acceleratedOrbit 18 212223 = 143413 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_212223 : ∀ j : Fin 18,
    212223 ≤ acceleratedOrbit j.val 212223 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_212223 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 212223) = 177147 * m + 143413 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 212223
  rw [data_18_212223.1, data_18_212223.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_212223 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 212223) < 262144 * m + 212223 := by
  apply descent_of_endpoint
  · rw [data_18_212223.1]; exact data_18_212223.2.2
  · rw [data_18_212223.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 212827). -/
theorem data_18_212827 : oddCount 212827 18 = 11 ∧
    acceleratedOrbit 18 212827 = 143822 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_212827 : ∀ j : Fin 18,
    212827 ≤ acceleratedOrbit j.val 212827 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_212827 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 212827) = 177147 * m + 143822 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 212827
  rw [data_18_212827.1, data_18_212827.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_212827 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 212827) < 262144 * m + 212827 := by
  apply descent_of_endpoint
  · rw [data_18_212827.1]; exact data_18_212827.2.2
  · rw [data_18_212827.2.1]; decide

end Collatz.Research.FirstDescent.Batch197
