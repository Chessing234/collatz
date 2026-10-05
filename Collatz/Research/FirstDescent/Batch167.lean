import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 167. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch167
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 141415). -/
theorem data_18_141415 : oddCount 141415 18 = 11 ∧
    acceleratedOrbit 18 141415 = 95564 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_141415 : ∀ j : Fin 18,
    141415 ≤ acceleratedOrbit j.val 141415 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_141415 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 141415) = 177147 * m + 95564 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 141415
  rw [data_18_141415.1, data_18_141415.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_141415 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 141415) < 262144 * m + 141415 := by
  apply descent_of_endpoint
  · rw [data_18_141415.1]; exact data_18_141415.2.2
  · rw [data_18_141415.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 143451). -/
theorem data_18_143451 : oddCount 143451 18 = 11 ∧
    acceleratedOrbit 18 143451 = 96940 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_143451 : ∀ j : Fin 18,
    143451 ≤ acceleratedOrbit j.val 143451 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_143451 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 143451) = 177147 * m + 96940 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 143451
  rw [data_18_143451.1, data_18_143451.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_143451 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 143451) < 262144 * m + 143451 := by
  apply descent_of_endpoint
  · rw [data_18_143451.1]; exact data_18_143451.2.2
  · rw [data_18_143451.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 143839). -/
theorem data_18_143839 : oddCount 143839 18 = 11 ∧
    acceleratedOrbit 18 143839 = 97202 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_143839 : ∀ j : Fin 18,
    143839 ≤ acceleratedOrbit j.val 143839 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_143839 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 143839) = 177147 * m + 97202 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 143839
  rw [data_18_143839.1, data_18_143839.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_143839 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 143839) < 262144 * m + 143839 := by
  apply descent_of_endpoint
  · rw [data_18_143839.1]; exact data_18_143839.2.2
  · rw [data_18_143839.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 143963). -/
theorem data_18_143963 : oddCount 143963 18 = 11 ∧
    acceleratedOrbit 18 143963 = 97286 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_143963 : ∀ j : Fin 18,
    143963 ≤ acceleratedOrbit j.val 143963 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_143963 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 143963) = 177147 * m + 97286 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 143963
  rw [data_18_143963.1, data_18_143963.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_143963 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 143963) < 262144 * m + 143963 := by
  apply descent_of_endpoint
  · rw [data_18_143963.1]; exact data_18_143963.2.2
  · rw [data_18_143963.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 144863). -/
theorem data_18_144863 : oddCount 144863 18 = 11 ∧
    acceleratedOrbit 18 144863 = 97894 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_144863 : ∀ j : Fin 18,
    144863 ≤ acceleratedOrbit j.val 144863 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_144863 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 144863) = 177147 * m + 97894 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 144863
  rw [data_18_144863.1, data_18_144863.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_144863 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 144863) < 262144 * m + 144863 := by
  apply descent_of_endpoint
  · rw [data_18_144863.1]; exact data_18_144863.2.2
  · rw [data_18_144863.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 144943). -/
theorem data_18_144943 : oddCount 144943 18 = 11 ∧
    acceleratedOrbit 18 144943 = 97948 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_144943 : ∀ j : Fin 18,
    144943 ≤ acceleratedOrbit j.val 144943 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_144943 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 144943) = 177147 * m + 97948 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 144943
  rw [data_18_144943.1, data_18_144943.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_144943 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 144943) < 262144 * m + 144943 := by
  apply descent_of_endpoint
  · rw [data_18_144943.1]; exact data_18_144943.2.2
  · rw [data_18_144943.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 145535). -/
theorem data_18_145535 : oddCount 145535 18 = 11 ∧
    acceleratedOrbit 18 145535 = 98348 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_145535 : ∀ j : Fin 18,
    145535 ≤ acceleratedOrbit j.val 145535 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_145535 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 145535) = 177147 * m + 98348 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 145535
  rw [data_18_145535.1, data_18_145535.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_145535 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 145535) < 262144 * m + 145535 := by
  apply descent_of_endpoint
  · rw [data_18_145535.1]; exact data_18_145535.2.2
  · rw [data_18_145535.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 146879). -/
theorem data_18_146879 : oddCount 146879 18 = 11 ∧
    acceleratedOrbit 18 146879 = 99256 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_146879 : ∀ j : Fin 18,
    146879 ≤ acceleratedOrbit j.val 146879 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_146879 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 146879) = 177147 * m + 99256 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 146879
  rw [data_18_146879.1, data_18_146879.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_146879 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 146879) < 262144 * m + 146879 := by
  apply descent_of_endpoint
  · rw [data_18_146879.1]; exact data_18_146879.2.2
  · rw [data_18_146879.2.1]; decide

end Collatz.Research.FirstDescent.Batch167
