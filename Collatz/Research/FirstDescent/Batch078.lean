import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 78. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch078
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 41723). -/
theorem data_16_41723 : oddCount 41723 16 = 10 ∧
    acceleratedOrbit 16 41723 = 37595 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_41723 : ∀ j : Fin 16,
    41723 ≤ acceleratedOrbit j.val 41723 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_41723 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 41723) = 59049 * m + 37595 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 41723
  rw [data_16_41723.1, data_16_41723.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_41723 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 41723) < 65536 * m + 41723 := by
  apply descent_of_endpoint
  · rw [data_16_41723.1]; exact data_16_41723.2.2
  · rw [data_16_41723.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 42075). -/
theorem data_16_42075 : oddCount 42075 16 = 10 ∧
    acceleratedOrbit 16 42075 = 37912 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_42075 : ∀ j : Fin 16,
    42075 ≤ acceleratedOrbit j.val 42075 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_42075 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 42075) = 59049 * m + 37912 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 42075
  rw [data_16_42075.1, data_16_42075.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_42075 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 42075) < 65536 * m + 42075 := by
  apply descent_of_endpoint
  · rw [data_16_42075.1]; exact data_16_42075.2.2
  · rw [data_16_42075.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 42215). -/
theorem data_16_42215 : oddCount 42215 16 = 10 ∧
    acceleratedOrbit 16 42215 = 38038 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_42215 : ∀ j : Fin 16,
    42215 ≤ acceleratedOrbit j.val 42215 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_42215 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 42215) = 59049 * m + 38038 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 42215
  rw [data_16_42215.1, data_16_42215.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_42215 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 42215) < 65536 * m + 42215 := by
  apply descent_of_endpoint
  · rw [data_16_42215.1]; exact data_16_42215.2.2
  · rw [data_16_42215.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 42239). -/
theorem data_16_42239 : oddCount 42239 16 = 10 ∧
    acceleratedOrbit 16 42239 = 38059 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_42239 : ∀ j : Fin 16,
    42239 ≤ acceleratedOrbit j.val 42239 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_42239 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 42239) = 59049 * m + 38059 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 42239
  rw [data_16_42239.1, data_16_42239.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_42239 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 42239) < 65536 * m + 42239 := by
  apply descent_of_endpoint
  · rw [data_16_42239.1]; exact data_16_42239.2.2
  · rw [data_16_42239.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 42303). -/
theorem data_16_42303 : oddCount 42303 16 = 10 ∧
    acceleratedOrbit 16 42303 = 38117 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_42303 : ∀ j : Fin 16,
    42303 ≤ acceleratedOrbit j.val 42303 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_42303 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 42303) = 59049 * m + 38117 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 42303
  rw [data_16_42303.1, data_16_42303.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_42303 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 42303) < 65536 * m + 42303 := by
  apply descent_of_endpoint
  · rw [data_16_42303.1]; exact data_16_42303.2.2
  · rw [data_16_42303.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 42343). -/
theorem data_16_42343 : oddCount 42343 16 = 10 ∧
    acceleratedOrbit 16 42343 = 38153 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_42343 : ∀ j : Fin 16,
    42343 ≤ acceleratedOrbit j.val 42343 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_42343 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 42343) = 59049 * m + 38153 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 42343
  rw [data_16_42343.1, data_16_42343.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_42343 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 42343) < 65536 * m + 42343 := by
  apply descent_of_endpoint
  · rw [data_16_42343.1]; exact data_16_42343.2.2
  · rw [data_16_42343.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 42471). -/
theorem data_16_42471 : oddCount 42471 16 = 10 ∧
    acceleratedOrbit 16 42471 = 38269 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_42471 : ∀ j : Fin 16,
    42471 ≤ acceleratedOrbit j.val 42471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_42471 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 42471) = 59049 * m + 38269 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 42471
  rw [data_16_42471.1, data_16_42471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_42471 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 42471) < 65536 * m + 42471 := by
  apply descent_of_endpoint
  · rw [data_16_42471.1]; exact data_16_42471.2.2
  · rw [data_16_42471.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 42651). -/
theorem data_16_42651 : oddCount 42651 16 = 10 ∧
    acceleratedOrbit 16 42651 = 38431 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_42651 : ∀ j : Fin 16,
    42651 ≤ acceleratedOrbit j.val 42651 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_42651 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 42651) = 59049 * m + 38431 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 42651
  rw [data_16_42651.1, data_16_42651.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_42651 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 42651) < 65536 * m + 42651 := by
  apply descent_of_endpoint
  · rw [data_16_42651.1]; exact data_16_42651.2.2
  · rw [data_16_42651.2.1]; decide

end Collatz.Research.FirstDescent.Batch078
