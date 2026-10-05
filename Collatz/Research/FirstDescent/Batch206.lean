import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 206. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch206
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 229403). -/
theorem data_18_229403 : oddCount 229403 18 = 11 ∧
    acceleratedOrbit 18 229403 = 155023 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_229403 : ∀ j : Fin 18,
    229403 ≤ acceleratedOrbit j.val 229403 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_229403 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 229403) = 177147 * m + 155023 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 229403
  rw [data_18_229403.1, data_18_229403.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_229403 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 229403) < 262144 * m + 229403 := by
  apply descent_of_endpoint
  · rw [data_18_229403.1]; exact data_18_229403.2.2
  · rw [data_18_229403.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 229447). -/
theorem data_18_229447 : oddCount 229447 18 = 11 ∧
    acceleratedOrbit 18 229447 = 155053 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_229447 : ∀ j : Fin 18,
    229447 ≤ acceleratedOrbit j.val 229447 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_229447 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 229447) = 177147 * m + 155053 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 229447
  rw [data_18_229447.1, data_18_229447.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_229447 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 229447) < 262144 * m + 229447 := by
  apply descent_of_endpoint
  · rw [data_18_229447.1]; exact data_18_229447.2.2
  · rw [data_18_229447.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 229871). -/
theorem data_18_229871 : oddCount 229871 18 = 11 ∧
    acceleratedOrbit 18 229871 = 155339 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_229871 : ∀ j : Fin 18,
    229871 ≤ acceleratedOrbit j.val 229871 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_229871 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 229871) = 177147 * m + 155339 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 229871
  rw [data_18_229871.1, data_18_229871.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_229871 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 229871) < 262144 * m + 229871 := by
  apply descent_of_endpoint
  · rw [data_18_229871.1]; exact data_18_229871.2.2
  · rw [data_18_229871.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 230047). -/
theorem data_18_230047 : oddCount 230047 18 = 11 ∧
    acceleratedOrbit 18 230047 = 155458 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_230047 : ∀ j : Fin 18,
    230047 ≤ acceleratedOrbit j.val 230047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_230047 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 230047) = 177147 * m + 155458 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 230047
  rw [data_18_230047.1, data_18_230047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_230047 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 230047) < 262144 * m + 230047 := by
  apply descent_of_endpoint
  · rw [data_18_230047.1]; exact data_18_230047.2.2
  · rw [data_18_230047.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 230127). -/
theorem data_18_230127 : oddCount 230127 18 = 11 ∧
    acceleratedOrbit 18 230127 = 155512 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_230127 : ∀ j : Fin 18,
    230127 ≤ acceleratedOrbit j.val 230127 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_230127 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 230127) = 177147 * m + 155512 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 230127
  rw [data_18_230127.1, data_18_230127.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_230127 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 230127) < 262144 * m + 230127 := by
  apply descent_of_endpoint
  · rw [data_18_230127.1]; exact data_18_230127.2.2
  · rw [data_18_230127.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 230559). -/
theorem data_18_230559 : oddCount 230559 18 = 11 ∧
    acceleratedOrbit 18 230559 = 155804 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_230559 : ∀ j : Fin 18,
    230559 ≤ acceleratedOrbit j.val 230559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_230559 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 230559) = 177147 * m + 155804 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 230559
  rw [data_18_230559.1, data_18_230559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_230559 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 230559) < 262144 * m + 230559 := by
  apply descent_of_endpoint
  · rw [data_18_230559.1]; exact data_18_230559.2.2
  · rw [data_18_230559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 230727). -/
theorem data_18_230727 : oddCount 230727 18 = 11 ∧
    acceleratedOrbit 18 230727 = 155918 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_230727 : ∀ j : Fin 18,
    230727 ≤ acceleratedOrbit j.val 230727 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_230727 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 230727) = 177147 * m + 155918 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 230727
  rw [data_18_230727.1, data_18_230727.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_230727 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 230727) < 262144 * m + 230727 := by
  apply descent_of_endpoint
  · rw [data_18_230727.1]; exact data_18_230727.2.2
  · rw [data_18_230727.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 231911). -/
theorem data_18_231911 : oddCount 231911 18 = 11 ∧
    acceleratedOrbit 18 231911 = 156718 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_231911 : ∀ j : Fin 18,
    231911 ≤ acceleratedOrbit j.val 231911 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_231911 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 231911) = 177147 * m + 156718 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 231911
  rw [data_18_231911.1, data_18_231911.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_231911 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 231911) < 262144 * m + 231911 := by
  apply descent_of_endpoint
  · rw [data_18_231911.1]; exact data_18_231911.2.2
  · rw [data_18_231911.2.1]; decide

end Collatz.Research.FirstDescent.Batch206
