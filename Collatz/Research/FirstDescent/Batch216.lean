import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 216. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch216
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 254655). -/
theorem data_18_254655 : oddCount 254655 18 = 11 ∧
    acceleratedOrbit 18 254655 = 172087 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_254655 : ∀ j : Fin 18,
    254655 ≤ acceleratedOrbit j.val 254655 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_254655 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 254655) = 177147 * m + 172087 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 254655
  rw [data_18_254655.1, data_18_254655.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_254655 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 254655) < 262144 * m + 254655 := by
  apply descent_of_endpoint
  · rw [data_18_254655.1]; exact data_18_254655.2.2
  · rw [data_18_254655.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 254847). -/
theorem data_18_254847 : oddCount 254847 18 = 11 ∧
    acceleratedOrbit 18 254847 = 172217 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_254847 : ∀ j : Fin 18,
    254847 ≤ acceleratedOrbit j.val 254847 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_254847 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 254847) = 177147 * m + 172217 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 254847
  rw [data_18_254847.1, data_18_254847.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_254847 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 254847) < 262144 * m + 254847 := by
  apply descent_of_endpoint
  · rw [data_18_254847.1]; exact data_18_254847.2.2
  · rw [data_18_254847.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 256603). -/
theorem data_18_256603 : oddCount 256603 18 = 11 ∧
    acceleratedOrbit 18 256603 = 173404 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_256603 : ∀ j : Fin 18,
    256603 ≤ acceleratedOrbit j.val 256603 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_256603 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 256603) = 177147 * m + 173404 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 256603
  rw [data_18_256603.1, data_18_256603.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_256603 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 256603) < 262144 * m + 256603 := by
  apply descent_of_endpoint
  · rw [data_18_256603.1]; exact data_18_256603.2.2
  · rw [data_18_256603.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 256703). -/
theorem data_18_256703 : oddCount 256703 18 = 11 ∧
    acceleratedOrbit 18 256703 = 173471 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_256703 : ∀ j : Fin 18,
    256703 ≤ acceleratedOrbit j.val 256703 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_256703 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 256703) = 177147 * m + 173471 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 256703
  rw [data_18_256703.1, data_18_256703.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_256703 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 256703) < 262144 * m + 256703 := by
  apply descent_of_endpoint
  · rw [data_18_256703.1]; exact data_18_256703.2.2
  · rw [data_18_256703.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 256959). -/
theorem data_18_256959 : oddCount 256959 18 = 11 ∧
    acceleratedOrbit 18 256959 = 173644 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_256959 : ∀ j : Fin 18,
    256959 ≤ acceleratedOrbit j.val 256959 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_256959 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 256959) = 177147 * m + 173644 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 256959
  rw [data_18_256959.1, data_18_256959.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_256959 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 256959) < 262144 * m + 256959 := by
  apply descent_of_endpoint
  · rw [data_18_256959.1]; exact data_18_256959.2.2
  · rw [data_18_256959.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 257115). -/
theorem data_18_257115 : oddCount 257115 18 = 11 ∧
    acceleratedOrbit 18 257115 = 173750 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_257115 : ∀ j : Fin 18,
    257115 ≤ acceleratedOrbit j.val 257115 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_257115 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 257115) = 177147 * m + 173750 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 257115
  rw [data_18_257115.1, data_18_257115.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_257115 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 257115) < 262144 * m + 257115 := by
  apply descent_of_endpoint
  · rw [data_18_257115.1]; exact data_18_257115.2.2
  · rw [data_18_257115.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 257275). -/
theorem data_18_257275 : oddCount 257275 18 = 11 ∧
    acceleratedOrbit 18 257275 = 173858 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_257275 : ∀ j : Fin 18,
    257275 ≤ acceleratedOrbit j.val 257275 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_257275 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 257275) = 177147 * m + 173858 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 257275
  rw [data_18_257275.1, data_18_257275.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_257275 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 257275) < 262144 * m + 257275 := by
  apply descent_of_endpoint
  · rw [data_18_257275.1]; exact data_18_257275.2.2
  · rw [data_18_257275.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 257471). -/
theorem data_18_257471 : oddCount 257471 18 = 11 ∧
    acceleratedOrbit 18 257471 = 173990 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_257471 : ∀ j : Fin 18,
    257471 ≤ acceleratedOrbit j.val 257471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_257471 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 257471) = 177147 * m + 173990 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 257471
  rw [data_18_257471.1, data_18_257471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_257471 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 257471) < 262144 * m + 257471 := by
  apply descent_of_endpoint
  · rw [data_18_257471.1]; exact data_18_257471.2.2
  · rw [data_18_257471.2.1]; decide

end Collatz.Research.FirstDescent.Batch216
