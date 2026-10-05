import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 203. -/
namespace Collatz.Research.RefinementAtlas.Batch203
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 268). -/
theorem data_9_268 : oddCount 268 9 = 4 ∧
    acceleratedOrbit 9 268 = 44 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_268 : gap 9 268 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_268 : threshold 9 268 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_268 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 268) = 81 * (2 * m) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 268
  rw [data_9_268.1, data_9_268.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_268 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 268) = 81 * (2 * m + 1) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 268
  rw [data_9_268.1, data_9_268.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_268 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 268) < 512 * (2 * m) + 268 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 268 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_268] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 268) < 512 * (2 * m) + 268 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_268 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 268) < 512 * (2 * m + 1) + 268 := by
  apply refinement_cleared (k := 9) (r := 268) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_268]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 269). -/
theorem data_9_269 : oddCount 269 9 = 4 ∧
    acceleratedOrbit 9 269 = 44 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_269 : gap 9 269 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_269 : threshold 9 269 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_269 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 269) = 81 * (2 * m) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 269
  rw [data_9_269.1, data_9_269.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_269 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 269) = 81 * (2 * m + 1) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 269
  rw [data_9_269.1, data_9_269.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_269 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 269) < 512 * (2 * m) + 269 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 269 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_269] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 269) < 512 * (2 * m) + 269 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_269 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 269) < 512 * (2 * m + 1) + 269 := by
  apply refinement_cleared (k := 9) (r := 269) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_269]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 270). -/
theorem data_9_270 : oddCount 270 9 = 4 ∧
    acceleratedOrbit 9 270 = 43 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_270 : gap 9 270 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_270 : threshold 9 270 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_270 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 270) = 81 * (2 * m) + 43 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 270
  rw [data_9_270.1, data_9_270.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_270 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 270) = 81 * (2 * m + 1) + 43 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 270
  rw [data_9_270.1, data_9_270.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_270 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 270) < 512 * (2 * m) + 270 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 270 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_270] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 270) < 512 * (2 * m) + 270 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_270 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 270) < 512 * (2 * m + 1) + 270 := by
  apply refinement_cleared (k := 9) (r := 270) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_270]; decide

end Collatz.Research.RefinementAtlas.Batch203
