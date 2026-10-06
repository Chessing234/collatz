import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 30. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch030
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 16863). -/
theorem data_15_16863 : oddCount 16863 15 = 9 ∧
    acceleratedOrbit 15 16863 = 10130 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_16863 : ∀ j : Fin 15,
    16863 ≤ acceleratedOrbit j.val 16863 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_16863 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 16863) = 19683 * m + 10130 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 16863
  rw [data_15_16863.1, data_15_16863.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_16863 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 16863) < 32768 * m + 16863 := by
  apply descent_of_endpoint
  · rw [data_15_16863.1]; exact data_15_16863.2.2
  · rw [data_15_16863.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 16871). -/
theorem data_15_16871 : oddCount 16871 15 = 9 ∧
    acceleratedOrbit 15 16871 = 10135 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_16871 : ∀ j : Fin 15,
    16871 ≤ acceleratedOrbit j.val 16871 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_16871 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 16871) = 19683 * m + 10135 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 16871
  rw [data_15_16871.1, data_15_16871.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_16871 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 16871) < 32768 * m + 16871 := by
  apply descent_of_endpoint
  · rw [data_15_16871.1]; exact data_15_16871.2.2
  · rw [data_15_16871.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 17147). -/
theorem data_15_17147 : oddCount 17147 15 = 9 ∧
    acceleratedOrbit 15 17147 = 10301 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_17147 : ∀ j : Fin 15,
    17147 ≤ acceleratedOrbit j.val 17147 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_17147 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 17147) = 19683 * m + 10301 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 17147
  rw [data_15_17147.1, data_15_17147.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_17147 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 17147) < 32768 * m + 17147 := by
  apply descent_of_endpoint
  · rw [data_15_17147.1]; exact data_15_17147.2.2
  · rw [data_15_17147.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 17727). -/
theorem data_15_17727 : oddCount 17727 15 = 9 ∧
    acceleratedOrbit 15 17727 = 10649 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_17727 : ∀ j : Fin 15,
    17727 ≤ acceleratedOrbit j.val 17727 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_17727 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 17727) = 19683 * m + 10649 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 17727
  rw [data_15_17727.1, data_15_17727.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_17727 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 17727) < 32768 * m + 17727 := by
  apply descent_of_endpoint
  · rw [data_15_17727.1]; exact data_15_17727.2.2
  · rw [data_15_17727.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 17735). -/
theorem data_15_17735 : oddCount 17735 15 = 9 ∧
    acceleratedOrbit 15 17735 = 10654 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_17735 : ∀ j : Fin 15,
    17735 ≤ acceleratedOrbit j.val 17735 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_17735 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 17735) = 19683 * m + 10654 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 17735
  rw [data_15_17735.1, data_15_17735.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_17735 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 17735) < 32768 * m + 17735 := by
  apply descent_of_endpoint
  · rw [data_15_17735.1]; exact data_15_17735.2.2
  · rw [data_15_17735.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 17767). -/
theorem data_15_17767 : oddCount 17767 15 = 9 ∧
    acceleratedOrbit 15 17767 = 10673 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_17767 : ∀ j : Fin 15,
    17767 ≤ acceleratedOrbit j.val 17767 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_17767 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 17767) = 19683 * m + 10673 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 17767
  rw [data_15_17767.1, data_15_17767.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_17767 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 17767) < 32768 * m + 17767 := by
  apply descent_of_endpoint
  · rw [data_15_17767.1]; exact data_15_17767.2.2
  · rw [data_15_17767.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 18011). -/
theorem data_15_18011 : oddCount 18011 15 = 9 ∧
    acceleratedOrbit 15 18011 = 10820 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_18011 : ∀ j : Fin 15,
    18011 ≤ acceleratedOrbit j.val 18011 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_18011 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 18011) = 19683 * m + 10820 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 18011
  rw [data_15_18011.1, data_15_18011.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_18011 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 18011) < 32768 * m + 18011 := by
  apply descent_of_endpoint
  · rw [data_15_18011.1]; exact data_15_18011.2.2
  · rw [data_15_18011.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 18639). -/
theorem data_15_18639 : oddCount 18639 15 = 9 ∧
    acceleratedOrbit 15 18639 = 11197 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_18639 : ∀ j : Fin 15,
    18639 ≤ acceleratedOrbit j.val 18639 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_18639 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 18639) = 19683 * m + 11197 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 18639
  rw [data_15_18639.1, data_15_18639.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_18639 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 18639) < 32768 * m + 18639 := by
  apply descent_of_endpoint
  · rw [data_15_18639.1]; exact data_15_18639.2.2
  · rw [data_15_18639.2.1]; decide

end Collatz.Research.FirstDescent.Batch030
