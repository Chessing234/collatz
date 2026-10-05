import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 204. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch204
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 225351). -/
theorem data_18_225351 : oddCount 225351 18 = 11 ∧
    acceleratedOrbit 18 225351 = 152285 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_225351 : ∀ j : Fin 18,
    225351 ≤ acceleratedOrbit j.val 225351 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_225351 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 225351) = 177147 * m + 152285 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 225351
  rw [data_18_225351.1, data_18_225351.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_225351 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 225351) < 262144 * m + 225351 := by
  apply descent_of_endpoint
  · rw [data_18_225351.1]; exact data_18_225351.2.2
  · rw [data_18_225351.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 225471). -/
theorem data_18_225471 : oddCount 225471 18 = 11 ∧
    acceleratedOrbit 18 225471 = 152366 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_225471 : ∀ j : Fin 18,
    225471 ≤ acceleratedOrbit j.val 225471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_225471 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 225471) = 177147 * m + 152366 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 225471
  rw [data_18_225471.1, data_18_225471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_225471 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 225471) < 262144 * m + 225471 := by
  apply descent_of_endpoint
  · rw [data_18_225471.1]; exact data_18_225471.2.2
  · rw [data_18_225471.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 225767). -/
theorem data_18_225767 : oddCount 225767 18 = 11 ∧
    acceleratedOrbit 18 225767 = 152566 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_225767 : ∀ j : Fin 18,
    225767 ≤ acceleratedOrbit j.val 225767 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_225767 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 225767) = 177147 * m + 152566 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 225767
  rw [data_18_225767.1, data_18_225767.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_225767 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 225767) < 262144 * m + 225767 := by
  apply descent_of_endpoint
  · rw [data_18_225767.1]; exact data_18_225767.2.2
  · rw [data_18_225767.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 225951). -/
theorem data_18_225951 : oddCount 225951 18 = 11 ∧
    acceleratedOrbit 18 225951 = 152690 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_225951 : ∀ j : Fin 18,
    225951 ≤ acceleratedOrbit j.val 225951 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_225951 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 225951) = 177147 * m + 152690 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 225951
  rw [data_18_225951.1, data_18_225951.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_225951 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 225951) < 262144 * m + 225951 := by
  apply descent_of_endpoint
  · rw [data_18_225951.1]; exact data_18_225951.2.2
  · rw [data_18_225951.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 225959). -/
theorem data_18_225959 : oddCount 225959 18 = 11 ∧
    acceleratedOrbit 18 225959 = 152696 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_225959 : ∀ j : Fin 18,
    225959 ≤ acceleratedOrbit j.val 225959 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_225959 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 225959) = 177147 * m + 152696 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 225959
  rw [data_18_225959.1, data_18_225959.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_225959 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 225959) < 262144 * m + 225959 := by
  apply descent_of_endpoint
  · rw [data_18_225959.1]; exact data_18_225959.2.2
  · rw [data_18_225959.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 225999). -/
theorem data_18_225999 : oddCount 225999 18 = 11 ∧
    acceleratedOrbit 18 225999 = 152723 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_225999 : ∀ j : Fin 18,
    225999 ≤ acceleratedOrbit j.val 225999 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_225999 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 225999) = 177147 * m + 152723 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 225999
  rw [data_18_225999.1, data_18_225999.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_225999 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 225999) < 262144 * m + 225999 := by
  apply descent_of_endpoint
  · rw [data_18_225999.1]; exact data_18_225999.2.2
  · rw [data_18_225999.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 226079). -/
theorem data_18_226079 : oddCount 226079 18 = 11 ∧
    acceleratedOrbit 18 226079 = 152777 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_226079 : ∀ j : Fin 18,
    226079 ≤ acceleratedOrbit j.val 226079 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_226079 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 226079) = 177147 * m + 152777 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 226079
  rw [data_18_226079.1, data_18_226079.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_226079 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 226079) < 262144 * m + 226079 := by
  apply descent_of_endpoint
  · rw [data_18_226079.1]; exact data_18_226079.2.2
  · rw [data_18_226079.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 226119). -/
theorem data_18_226119 : oddCount 226119 18 = 11 ∧
    acceleratedOrbit 18 226119 = 152804 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_226119 : ∀ j : Fin 18,
    226119 ≤ acceleratedOrbit j.val 226119 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_226119 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 226119) = 177147 * m + 152804 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 226119
  rw [data_18_226119.1, data_18_226119.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_226119 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 226119) < 262144 * m + 226119 := by
  apply descent_of_endpoint
  · rw [data_18_226119.1]; exact data_18_226119.2.2
  · rw [data_18_226119.2.1]; decide

end Collatz.Research.FirstDescent.Batch204
