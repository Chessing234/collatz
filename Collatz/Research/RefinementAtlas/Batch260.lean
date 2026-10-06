import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 260. -/
namespace Collatz.Research.RefinementAtlas.Batch260
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 496). -/
theorem data_9_496 : oddCount 496 9 = 5 ∧
    acceleratedOrbit 9 496 = 242 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_496 : gap 9 496 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_496 : threshold 9 496 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_496 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 496) = 243 * (2 * m) + 242 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 496
  rw [data_9_496.1, data_9_496.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_496 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 496) = 243 * (2 * m + 1) + 242 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 496
  rw [data_9_496.1, data_9_496.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_496 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 496) < 512 * (2 * m) + 496 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 496 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_496] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 496) < 512 * (2 * m) + 496 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_496 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 496) < 512 * (2 * m + 1) + 496 := by
  apply refinement_cleared (k := 9) (r := 496) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_496]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 497). -/
theorem data_9_497 : oddCount 497 9 = 4 ∧
    acceleratedOrbit 9 497 = 80 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_497 : gap 9 497 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_497 : threshold 9 497 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_497 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 497) = 81 * (2 * m) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 497
  rw [data_9_497.1, data_9_497.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_497 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 497) = 81 * (2 * m + 1) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 497
  rw [data_9_497.1, data_9_497.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_497 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 497) < 512 * (2 * m) + 497 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 497 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_497] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 497) < 512 * (2 * m) + 497 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_497 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 497) < 512 * (2 * m + 1) + 497 := by
  apply refinement_cleared (k := 9) (r := 497) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_497]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 498). -/
theorem data_9_498 : oddCount 498 9 = 5 ∧
    acceleratedOrbit 9 498 = 238 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_498 : gap 9 498 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_498 : threshold 9 498 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_498 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 498) = 243 * (2 * m) + 238 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 498
  rw [data_9_498.1, data_9_498.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_498 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 498) = 243 * (2 * m + 1) + 238 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 498
  rw [data_9_498.1, data_9_498.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_498 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 498) < 512 * (2 * m) + 498 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 498 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_498] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 498) < 512 * (2 * m) + 498 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_498 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 498) < 512 * (2 * m + 1) + 498 := by
  apply refinement_cleared (k := 9) (r := 498) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_498]; decide

end Collatz.Research.RefinementAtlas.Batch260
