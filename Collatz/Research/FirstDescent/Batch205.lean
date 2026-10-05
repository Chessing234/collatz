import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 205. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch205
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 226331). -/
theorem data_18_226331 : oddCount 226331 18 = 11 ∧
    acceleratedOrbit 18 226331 = 152947 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_226331 : ∀ j : Fin 18,
    226331 ≤ acceleratedOrbit j.val 226331 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_226331 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 226331) = 177147 * m + 152947 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 226331
  rw [data_18_226331.1, data_18_226331.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_226331 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 226331) < 262144 * m + 226331 := by
  apply descent_of_endpoint
  · rw [data_18_226331.1]; exact data_18_226331.2.2
  · rw [data_18_226331.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 226559). -/
theorem data_18_226559 : oddCount 226559 18 = 11 ∧
    acceleratedOrbit 18 226559 = 153101 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_226559 : ∀ j : Fin 18,
    226559 ≤ acceleratedOrbit j.val 226559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_226559 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 226559) = 177147 * m + 153101 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 226559
  rw [data_18_226559.1, data_18_226559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_226559 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 226559) < 262144 * m + 226559 := by
  apply descent_of_endpoint
  · rw [data_18_226559.1]; exact data_18_226559.2.2
  · rw [data_18_226559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 227567). -/
theorem data_18_227567 : oddCount 227567 18 = 11 ∧
    acceleratedOrbit 18 227567 = 153782 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_227567 : ∀ j : Fin 18,
    227567 ≤ acceleratedOrbit j.val 227567 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_227567 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 227567) = 177147 * m + 153782 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 227567
  rw [data_18_227567.1, data_18_227567.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_227567 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 227567) < 262144 * m + 227567 := by
  apply descent_of_endpoint
  · rw [data_18_227567.1]; exact data_18_227567.2.2
  · rw [data_18_227567.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 228347). -/
theorem data_18_228347 : oddCount 228347 18 = 11 ∧
    acceleratedOrbit 18 228347 = 154310 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_228347 : ∀ j : Fin 18,
    228347 ≤ acceleratedOrbit j.val 228347 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_228347 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 228347) = 177147 * m + 154310 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 228347
  rw [data_18_228347.1, data_18_228347.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_228347 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 228347) < 262144 * m + 228347 := by
  apply descent_of_endpoint
  · rw [data_18_228347.1]; exact data_18_228347.2.2
  · rw [data_18_228347.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 228591). -/
theorem data_18_228591 : oddCount 228591 18 = 11 ∧
    acceleratedOrbit 18 228591 = 154474 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_228591 : ∀ j : Fin 18,
    228591 ≤ acceleratedOrbit j.val 228591 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_228591 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 228591) = 177147 * m + 154474 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 228591
  rw [data_18_228591.1, data_18_228591.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_228591 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 228591) < 262144 * m + 228591 := by
  apply descent_of_endpoint
  · rw [data_18_228591.1]; exact data_18_228591.2.2
  · rw [data_18_228591.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 228635). -/
theorem data_18_228635 : oddCount 228635 18 = 11 ∧
    acceleratedOrbit 18 228635 = 154504 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_228635 : ∀ j : Fin 18,
    228635 ≤ acceleratedOrbit j.val 228635 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_228635 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 228635) = 177147 * m + 154504 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 228635
  rw [data_18_228635.1, data_18_228635.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_228635 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 228635) < 262144 * m + 228635 := by
  apply descent_of_endpoint
  · rw [data_18_228635.1]; exact data_18_228635.2.2
  · rw [data_18_228635.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 229023). -/
theorem data_18_229023 : oddCount 229023 18 = 11 ∧
    acceleratedOrbit 18 229023 = 154766 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_229023 : ∀ j : Fin 18,
    229023 ≤ acceleratedOrbit j.val 229023 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_229023 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 229023) = 177147 * m + 154766 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 229023
  rw [data_18_229023.1, data_18_229023.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_229023 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 229023) < 262144 * m + 229023 := by
  apply descent_of_endpoint
  · rw [data_18_229023.1]; exact data_18_229023.2.2
  · rw [data_18_229023.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 229115). -/
theorem data_18_229115 : oddCount 229115 18 = 11 ∧
    acceleratedOrbit 18 229115 = 154829 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_229115 : ∀ j : Fin 18,
    229115 ≤ acceleratedOrbit j.val 229115 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_229115 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 229115) = 177147 * m + 154829 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 229115
  rw [data_18_229115.1, data_18_229115.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_229115 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 229115) < 262144 * m + 229115 := by
  apply descent_of_endpoint
  · rw [data_18_229115.1]; exact data_18_229115.2.2
  · rw [data_18_229115.2.1]; decide

end Collatz.Research.FirstDescent.Batch205
