import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 61. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch061
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 23707). -/
theorem data_16_23707 : oddCount 23707 16 = 10 ∧
    acceleratedOrbit 16 23707 = 21362 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_23707 : ∀ j : Fin 16,
    23707 ≤ acceleratedOrbit j.val 23707 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_23707 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 23707) = 59049 * m + 21362 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 23707
  rw [data_16_23707.1, data_16_23707.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_23707 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 23707) < 65536 * m + 23707 := by
  apply descent_of_endpoint
  · rw [data_16_23707.1]; exact data_16_23707.2.2
  · rw [data_16_23707.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 23711). -/
theorem data_16_23711 : oddCount 23711 16 = 10 ∧
    acceleratedOrbit 16 23711 = 21365 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_23711 : ∀ j : Fin 16,
    23711 ≤ acceleratedOrbit j.val 23711 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_23711 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 23711) = 59049 * m + 21365 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 23711
  rw [data_16_23711.1, data_16_23711.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_23711 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 23711) < 65536 * m + 23711 := by
  apply descent_of_endpoint
  · rw [data_16_23711.1]; exact data_16_23711.2.2
  · rw [data_16_23711.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 23743). -/
theorem data_16_23743 : oddCount 23743 16 = 10 ∧
    acceleratedOrbit 16 23743 = 21394 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_23743 : ∀ j : Fin 16,
    23743 ≤ acceleratedOrbit j.val 23743 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_23743 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 23743) = 59049 * m + 21394 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 23743
  rw [data_16_23743.1, data_16_23743.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_23743 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 23743) < 65536 * m + 23743 := by
  apply descent_of_endpoint
  · rw [data_16_23743.1]; exact data_16_23743.2.2
  · rw [data_16_23743.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 23963). -/
theorem data_16_23963 : oddCount 23963 16 = 10 ∧
    acceleratedOrbit 16 23963 = 21593 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_23963 : ∀ j : Fin 16,
    23963 ≤ acceleratedOrbit j.val 23963 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_23963 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 23963) = 59049 * m + 21593 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 23963
  rw [data_16_23963.1, data_16_23963.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_23963 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 23963) < 65536 * m + 23963 := by
  apply descent_of_endpoint
  · rw [data_16_23963.1]; exact data_16_23963.2.2
  · rw [data_16_23963.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 24047). -/
theorem data_16_24047 : oddCount 24047 16 = 10 ∧
    acceleratedOrbit 16 24047 = 21668 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_24047 : ∀ j : Fin 16,
    24047 ≤ acceleratedOrbit j.val 24047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_24047 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 24047) = 59049 * m + 21668 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 24047
  rw [data_16_24047.1, data_16_24047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_24047 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 24047) < 65536 * m + 24047 := by
  apply descent_of_endpoint
  · rw [data_16_24047.1]; exact data_16_24047.2.2
  · rw [data_16_24047.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 24383). -/
theorem data_16_24383 : oddCount 24383 16 = 10 ∧
    acceleratedOrbit 16 24383 = 21971 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_24383 : ∀ j : Fin 16,
    24383 ≤ acceleratedOrbit j.val 24383 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_24383 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 24383) = 59049 * m + 21971 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 24383
  rw [data_16_24383.1, data_16_24383.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_24383 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 24383) < 65536 * m + 24383 := by
  apply descent_of_endpoint
  · rw [data_16_24383.1]; exact data_16_24383.2.2
  · rw [data_16_24383.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 24571). -/
theorem data_16_24571 : oddCount 24571 16 = 10 ∧
    acceleratedOrbit 16 24571 = 22141 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_24571 : ∀ j : Fin 16,
    24571 ≤ acceleratedOrbit j.val 24571 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_24571 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 24571) = 59049 * m + 22141 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 24571
  rw [data_16_24571.1, data_16_24571.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_24571 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 24571) < 65536 * m + 24571 := by
  apply descent_of_endpoint
  · rw [data_16_24571.1]; exact data_16_24571.2.2
  · rw [data_16_24571.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 24703). -/
theorem data_16_24703 : oddCount 24703 16 = 10 ∧
    acceleratedOrbit 16 24703 = 22259 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_24703 : ∀ j : Fin 16,
    24703 ≤ acceleratedOrbit j.val 24703 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_24703 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 24703) = 59049 * m + 22259 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 24703
  rw [data_16_24703.1, data_16_24703.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_24703 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 24703) < 65536 * m + 24703 := by
  apply descent_of_endpoint
  · rw [data_16_24703.1]; exact data_16_24703.2.2
  · rw [data_16_24703.2.1]; decide

end Collatz.Research.FirstDescent.Batch061
