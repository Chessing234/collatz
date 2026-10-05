import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 239. -/
namespace Collatz.Research.RefinementAtlas.Batch239
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 405). -/
theorem data_9_405 : oddCount 405 9 = 3 ∧
    acceleratedOrbit 9 405 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_405 : gap 9 405 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_405 : threshold 9 405 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_405 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 405) = 27 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 405
  rw [data_9_405.1, data_9_405.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_405 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 405) = 27 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 405
  rw [data_9_405.1, data_9_405.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_405 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 405) < 512 * (2 * m) + 405 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 405 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_405] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 405) < 512 * (2 * m) + 405 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_405 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 405) < 512 * (2 * m + 1) + 405 := by
  apply refinement_cleared (k := 9) (r := 405) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_405]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 406). -/
theorem data_9_406 : oddCount 406 9 = 4 ∧
    acceleratedOrbit 9 406 = 65 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_406 : gap 9 406 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_406 : threshold 9 406 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_406 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 406) = 81 * (2 * m) + 65 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 406
  rw [data_9_406.1, data_9_406.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_406 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 406) = 81 * (2 * m + 1) + 65 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 406
  rw [data_9_406.1, data_9_406.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_406 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 406) < 512 * (2 * m) + 406 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 406 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_406] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 406) < 512 * (2 * m) + 406 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_406 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 406) < 512 * (2 * m + 1) + 406 := by
  apply refinement_cleared (k := 9) (r := 406) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_406]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 407). -/
theorem data_9_407 : oddCount 407 9 = 4 ∧
    acceleratedOrbit 9 407 = 65 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_407 : gap 9 407 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_407 : threshold 9 407 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_407 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 407) = 81 * (2 * m) + 65 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 407
  rw [data_9_407.1, data_9_407.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_407 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 407) = 81 * (2 * m + 1) + 65 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 407
  rw [data_9_407.1, data_9_407.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_407 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 407) < 512 * (2 * m) + 407 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 407 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_407] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 407) < 512 * (2 * m) + 407 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_407 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 407) < 512 * (2 * m + 1) + 407 := by
  apply refinement_cleared (k := 9) (r := 407) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_407]; decide

end Collatz.Research.RefinementAtlas.Batch239
