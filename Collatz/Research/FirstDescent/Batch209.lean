import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 209. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch209
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 237183). -/
theorem data_18_237183 : oddCount 237183 18 = 11 ∧
    acceleratedOrbit 18 237183 = 160280 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_237183 : ∀ j : Fin 18,
    237183 ≤ acceleratedOrbit j.val 237183 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_237183 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 237183) = 177147 * m + 160280 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 237183
  rw [data_18_237183.1, data_18_237183.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_237183 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 237183) < 262144 * m + 237183 := by
  apply descent_of_endpoint
  · rw [data_18_237183.1]; exact data_18_237183.2.2
  · rw [data_18_237183.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 237471). -/
theorem data_18_237471 : oddCount 237471 18 = 11 ∧
    acceleratedOrbit 18 237471 = 160475 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_237471 : ∀ j : Fin 18,
    237471 ≤ acceleratedOrbit j.val 237471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_237471 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 237471) = 177147 * m + 160475 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 237471
  rw [data_18_237471.1, data_18_237471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_237471 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 237471) < 262144 * m + 237471 := by
  apply descent_of_endpoint
  · rw [data_18_237471.1]; exact data_18_237471.2.2
  · rw [data_18_237471.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 237639). -/
theorem data_18_237639 : oddCount 237639 18 = 11 ∧
    acceleratedOrbit 18 237639 = 160589 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_237639 : ∀ j : Fin 18,
    237639 ≤ acceleratedOrbit j.val 237639 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_237639 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 237639) = 177147 * m + 160589 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 237639
  rw [data_18_237639.1, data_18_237639.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_237639 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 237639) < 262144 * m + 237639 := by
  apply descent_of_endpoint
  · rw [data_18_237639.1]; exact data_18_237639.2.2
  · rw [data_18_237639.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 238207). -/
theorem data_18_238207 : oddCount 238207 18 = 11 ∧
    acceleratedOrbit 18 238207 = 160972 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_238207 : ∀ j : Fin 18,
    238207 ≤ acceleratedOrbit j.val 238207 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_238207 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 238207) = 177147 * m + 160972 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 238207
  rw [data_18_238207.1, data_18_238207.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_238207 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 238207) < 262144 * m + 238207 := by
  apply descent_of_endpoint
  · rw [data_18_238207.1]; exact data_18_238207.2.2
  · rw [data_18_238207.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 238239). -/
theorem data_18_238239 : oddCount 238239 18 = 11 ∧
    acceleratedOrbit 18 238239 = 160994 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_238239 : ∀ j : Fin 18,
    238239 ≤ acceleratedOrbit j.val 238239 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_238239 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 238239) = 177147 * m + 160994 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 238239
  rw [data_18_238239.1, data_18_238239.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_238239 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 238239) < 262144 * m + 238239 := by
  apply descent_of_endpoint
  · rw [data_18_238239.1]; exact data_18_238239.2.2
  · rw [data_18_238239.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 238663). -/
theorem data_18_238663 : oddCount 238663 18 = 11 ∧
    acceleratedOrbit 18 238663 = 161281 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_238663 : ∀ j : Fin 18,
    238663 ≤ acceleratedOrbit j.val 238663 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_238663 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 238663) = 177147 * m + 161281 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 238663
  rw [data_18_238663.1, data_18_238663.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_238663 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 238663) < 262144 * m + 238663 := by
  apply descent_of_endpoint
  · rw [data_18_238663.1]; exact data_18_238663.2.2
  · rw [data_18_238663.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 239343). -/
theorem data_18_239343 : oddCount 239343 18 = 11 ∧
    acceleratedOrbit 18 239343 = 161740 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_239343 : ∀ j : Fin 18,
    239343 ≤ acceleratedOrbit j.val 239343 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_239343 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 239343) = 177147 * m + 161740 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 239343
  rw [data_18_239343.1, data_18_239343.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_239343 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 239343) < 262144 * m + 239343 := by
  apply descent_of_endpoint
  · rw [data_18_239343.1]; exact data_18_239343.2.2
  · rw [data_18_239343.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 239935). -/
theorem data_18_239935 : oddCount 239935 18 = 11 ∧
    acceleratedOrbit 18 239935 = 162140 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_239935 : ∀ j : Fin 18,
    239935 ≤ acceleratedOrbit j.val 239935 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_239935 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 239935) = 177147 * m + 162140 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 239935
  rw [data_18_239935.1, data_18_239935.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_239935 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 239935) < 262144 * m + 239935 := by
  apply descent_of_endpoint
  · rw [data_18_239935.1]; exact data_18_239935.2.2
  · rw [data_18_239935.2.1]; decide

end Collatz.Research.FirstDescent.Batch209
