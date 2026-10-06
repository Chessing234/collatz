import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 201. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch201
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 219047). -/
theorem data_18_219047 : oddCount 219047 18 = 11 ∧
    acceleratedOrbit 18 219047 = 148025 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_219047 : ∀ j : Fin 18,
    219047 ≤ acceleratedOrbit j.val 219047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_219047 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 219047) = 177147 * m + 148025 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 219047
  rw [data_18_219047.1, data_18_219047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_219047 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 219047) < 262144 * m + 219047 := by
  apply descent_of_endpoint
  · rw [data_18_219047.1]; exact data_18_219047.2.2
  · rw [data_18_219047.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 219131). -/
theorem data_18_219131 : oddCount 219131 18 = 11 ∧
    acceleratedOrbit 18 219131 = 148082 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_219131 : ∀ j : Fin 18,
    219131 ≤ acceleratedOrbit j.val 219131 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_219131 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 219131) = 177147 * m + 148082 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 219131
  rw [data_18_219131.1, data_18_219131.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_219131 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 219131) < 262144 * m + 219131 := by
  apply descent_of_endpoint
  · rw [data_18_219131.1]; exact data_18_219131.2.2
  · rw [data_18_219131.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 219167). -/
theorem data_18_219167 : oddCount 219167 18 = 11 ∧
    acceleratedOrbit 18 219167 = 148106 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_219167 : ∀ j : Fin 18,
    219167 ≤ acceleratedOrbit j.val 219167 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_219167 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 219167) = 177147 * m + 148106 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 219167
  rw [data_18_219167.1, data_18_219167.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_219167 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 219167) < 262144 * m + 219167 := by
  apply descent_of_endpoint
  · rw [data_18_219167.1]; exact data_18_219167.2.2
  · rw [data_18_219167.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 219247). -/
theorem data_18_219247 : oddCount 219247 18 = 11 ∧
    acceleratedOrbit 18 219247 = 148160 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_219247 : ∀ j : Fin 18,
    219247 ≤ acceleratedOrbit j.val 219247 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_219247 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 219247) = 177147 * m + 148160 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 219247
  rw [data_18_219247.1, data_18_219247.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_219247 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 219247) < 262144 * m + 219247 := by
  apply descent_of_endpoint
  · rw [data_18_219247.1]; exact data_18_219247.2.2
  · rw [data_18_219247.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 219899). -/
theorem data_18_219899 : oddCount 219899 18 = 11 ∧
    acceleratedOrbit 18 219899 = 148601 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_219899 : ∀ j : Fin 18,
    219899 ≤ acceleratedOrbit j.val 219899 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_219899 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 219899) = 177147 * m + 148601 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 219899
  rw [data_18_219899.1, data_18_219899.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_219899 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 219899) < 262144 * m + 219899 := by
  apply descent_of_endpoint
  · rw [data_18_219899.1]; exact data_18_219899.2.2
  · rw [data_18_219899.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 220923). -/
theorem data_18_220923 : oddCount 220923 18 = 11 ∧
    acceleratedOrbit 18 220923 = 149293 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_220923 : ∀ j : Fin 18,
    220923 ≤ acceleratedOrbit j.val 220923 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_220923 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 220923) = 177147 * m + 149293 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 220923
  rw [data_18_220923.1, data_18_220923.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_220923 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 220923) < 262144 * m + 220923 := by
  apply descent_of_endpoint
  · rw [data_18_220923.1]; exact data_18_220923.2.2
  · rw [data_18_220923.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 220955). -/
theorem data_18_220955 : oddCount 220955 18 = 11 ∧
    acceleratedOrbit 18 220955 = 149314 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_220955 : ∀ j : Fin 18,
    220955 ≤ acceleratedOrbit j.val 220955 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_220955 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 220955) = 177147 * m + 149314 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 220955
  rw [data_18_220955.1, data_18_220955.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_220955 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 220955) < 262144 * m + 220955 := by
  apply descent_of_endpoint
  · rw [data_18_220955.1]; exact data_18_220955.2.2
  · rw [data_18_220955.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 221343). -/
theorem data_18_221343 : oddCount 221343 18 = 11 ∧
    acceleratedOrbit 18 221343 = 149576 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_221343 : ∀ j : Fin 18,
    221343 ≤ acceleratedOrbit j.val 221343 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_221343 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 221343) = 177147 * m + 149576 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 221343
  rw [data_18_221343.1, data_18_221343.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_221343 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 221343) < 262144 * m + 221343 := by
  apply descent_of_endpoint
  · rw [data_18_221343.1]; exact data_18_221343.2.2
  · rw [data_18_221343.2.1]; decide

end Collatz.Research.FirstDescent.Batch201
