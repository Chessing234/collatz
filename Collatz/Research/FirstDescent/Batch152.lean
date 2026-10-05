import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 152. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch152
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 109343). -/
theorem data_18_109343 : oddCount 109343 18 = 11 ∧
    acceleratedOrbit 18 109343 = 73891 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_109343 : ∀ j : Fin 18,
    109343 ≤ acceleratedOrbit j.val 109343 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_109343 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 109343) = 177147 * m + 73891 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 109343
  rw [data_18_109343.1, data_18_109343.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_109343 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 109343) < 262144 * m + 109343 := by
  apply descent_of_endpoint
  · rw [data_18_109343.1]; exact data_18_109343.2.2
  · rw [data_18_109343.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 109735). -/
theorem data_18_109735 : oddCount 109735 18 = 11 ∧
    acceleratedOrbit 18 109735 = 74156 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_109735 : ∀ j : Fin 18,
    109735 ≤ acceleratedOrbit j.val 109735 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_109735 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 109735) = 177147 * m + 74156 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 109735
  rw [data_18_109735.1, data_18_109735.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_109735 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 109735) < 262144 * m + 109735 := by
  apply descent_of_endpoint
  · rw [data_18_109735.1]; exact data_18_109735.2.2
  · rw [data_18_109735.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 109823). -/
theorem data_18_109823 : oddCount 109823 18 = 11 ∧
    acceleratedOrbit 18 109823 = 74215 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_109823 : ∀ j : Fin 18,
    109823 ≤ acceleratedOrbit j.val 109823 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_109823 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 109823) = 177147 * m + 74215 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 109823
  rw [data_18_109823.1, data_18_109823.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_109823 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 109823) < 262144 * m + 109823 := by
  apply descent_of_endpoint
  · rw [data_18_109823.1]; exact data_18_109823.2.2
  · rw [data_18_109823.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 110623). -/
theorem data_18_110623 : oddCount 110623 18 = 11 ∧
    acceleratedOrbit 18 110623 = 74756 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_110623 : ∀ j : Fin 18,
    110623 ≤ acceleratedOrbit j.val 110623 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_110623 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 110623) = 177147 * m + 74756 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 110623
  rw [data_18_110623.1, data_18_110623.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_110623 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 110623) < 262144 * m + 110623 := by
  apply descent_of_endpoint
  · rw [data_18_110623.1]; exact data_18_110623.2.2
  · rw [data_18_110623.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 111103). -/
theorem data_18_111103 : oddCount 111103 18 = 11 ∧
    acceleratedOrbit 18 111103 = 75080 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_111103 : ∀ j : Fin 18,
    111103 ≤ acceleratedOrbit j.val 111103 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_111103 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 111103) = 177147 * m + 75080 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 111103
  rw [data_18_111103.1, data_18_111103.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_111103 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 111103) < 262144 * m + 111103 := by
  apply descent_of_endpoint
  · rw [data_18_111103.1]; exact data_18_111103.2.2
  · rw [data_18_111103.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 111727). -/
theorem data_18_111727 : oddCount 111727 18 = 11 ∧
    acceleratedOrbit 18 111727 = 75502 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_111727 : ∀ j : Fin 18,
    111727 ≤ acceleratedOrbit j.val 111727 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_111727 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 111727) = 177147 * m + 75502 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 111727
  rw [data_18_111727.1, data_18_111727.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_111727 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 111727) < 262144 * m + 111727 := by
  apply descent_of_endpoint
  · rw [data_18_111727.1]; exact data_18_111727.2.2
  · rw [data_18_111727.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 111807). -/
theorem data_18_111807 : oddCount 111807 18 = 11 ∧
    acceleratedOrbit 18 111807 = 75556 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_111807 : ∀ j : Fin 18,
    111807 ≤ acceleratedOrbit j.val 111807 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_111807 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 111807) = 177147 * m + 75556 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 111807
  rw [data_18_111807.1, data_18_111807.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_111807 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 111807) < 262144 * m + 111807 := by
  apply descent_of_endpoint
  · rw [data_18_111807.1]; exact data_18_111807.2.2
  · rw [data_18_111807.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 111839). -/
theorem data_18_111839 : oddCount 111839 18 = 11 ∧
    acceleratedOrbit 18 111839 = 75578 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_111839 : ∀ j : Fin 18,
    111839 ≤ acceleratedOrbit j.val 111839 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_111839 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 111839) = 177147 * m + 75578 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 111839
  rw [data_18_111839.1, data_18_111839.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_111839 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 111839) < 262144 * m + 111839 := by
  apply descent_of_endpoint
  · rw [data_18_111839.1]; exact data_18_111839.2.2
  · rw [data_18_111839.2.1]; decide

end Collatz.Research.FirstDescent.Batch152
