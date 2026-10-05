import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 124. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch124
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 52991). -/
theorem data_18_52991 : oddCount 52991 18 = 11 ∧
    acceleratedOrbit 18 52991 = 35810 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_52991 : ∀ j : Fin 18,
    52991 ≤ acceleratedOrbit j.val 52991 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_52991 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 52991) = 177147 * m + 35810 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 52991
  rw [data_18_52991.1, data_18_52991.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_52991 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 52991) < 262144 * m + 52991 := by
  apply descent_of_endpoint
  · rw [data_18_52991.1]; exact data_18_52991.2.2
  · rw [data_18_52991.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 53279). -/
theorem data_18_53279 : oddCount 53279 18 = 11 ∧
    acceleratedOrbit 18 53279 = 36005 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_53279 : ∀ j : Fin 18,
    53279 ≤ acceleratedOrbit j.val 53279 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_53279 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 53279) = 177147 * m + 36005 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 53279
  rw [data_18_53279.1, data_18_53279.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_53279 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 53279) < 262144 * m + 53279 := by
  apply descent_of_endpoint
  · rw [data_18_53279.1]; exact data_18_53279.2.2
  · rw [data_18_53279.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 53359). -/
theorem data_18_53359 : oddCount 53359 18 = 11 ∧
    acceleratedOrbit 18 53359 = 36059 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_53359 : ∀ j : Fin 18,
    53359 ≤ acceleratedOrbit j.val 53359 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_53359 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 53359) = 177147 * m + 36059 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 53359
  rw [data_18_53359.1, data_18_53359.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_53359 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 53359) < 262144 * m + 53359 := by
  apply descent_of_endpoint
  · rw [data_18_53359.1]; exact data_18_53359.2.2
  · rw [data_18_53359.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 53759). -/
theorem data_18_53759 : oddCount 53759 18 = 11 ∧
    acceleratedOrbit 18 53759 = 36329 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_53759 : ∀ j : Fin 18,
    53759 ≤ acceleratedOrbit j.val 53759 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_53759 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 53759) = 177147 * m + 36329 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 53759
  rw [data_18_53759.1, data_18_53759.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_53759 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 53759) < 262144 * m + 53759 := by
  apply descent_of_endpoint
  · rw [data_18_53759.1]; exact data_18_53759.2.2
  · rw [data_18_53759.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 53807). -/
theorem data_18_53807 : oddCount 53807 18 = 11 ∧
    acceleratedOrbit 18 53807 = 36362 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_53807 : ∀ j : Fin 18,
    53807 ≤ acceleratedOrbit j.val 53807 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_53807 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 53807) = 177147 * m + 36362 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 53807
  rw [data_18_53807.1, data_18_53807.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_53807 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 53807) < 262144 * m + 53807 := by
  apply descent_of_endpoint
  · rw [data_18_53807.1]; exact data_18_53807.2.2
  · rw [data_18_53807.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 54015). -/
theorem data_18_54015 : oddCount 54015 18 = 11 ∧
    acceleratedOrbit 18 54015 = 36502 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_54015 : ∀ j : Fin 18,
    54015 ≤ acceleratedOrbit j.val 54015 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_54015 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 54015) = 177147 * m + 36502 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 54015
  rw [data_18_54015.1, data_18_54015.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_54015 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 54015) < 262144 * m + 54015 := by
  apply descent_of_endpoint
  · rw [data_18_54015.1]; exact data_18_54015.2.2
  · rw [data_18_54015.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 54991). -/
theorem data_18_54991 : oddCount 54991 18 = 11 ∧
    acceleratedOrbit 18 54991 = 37162 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_54991 : ∀ j : Fin 18,
    54991 ≤ acceleratedOrbit j.val 54991 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_54991 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 54991) = 177147 * m + 37162 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 54991
  rw [data_18_54991.1, data_18_54991.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_54991 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 54991) < 262144 * m + 54991 := by
  apply descent_of_endpoint
  · rw [data_18_54991.1]; exact data_18_54991.2.2
  · rw [data_18_54991.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 55231). -/
theorem data_18_55231 : oddCount 55231 18 = 11 ∧
    acceleratedOrbit 18 55231 = 37324 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_55231 : ∀ j : Fin 18,
    55231 ≤ acceleratedOrbit j.val 55231 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_55231 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 55231) = 177147 * m + 37324 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 55231
  rw [data_18_55231.1, data_18_55231.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_55231 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 55231) < 262144 * m + 55231 := by
  apply descent_of_endpoint
  · rw [data_18_55231.1]; exact data_18_55231.2.2
  · rw [data_18_55231.2.1]; decide

end Collatz.Research.FirstDescent.Batch124
