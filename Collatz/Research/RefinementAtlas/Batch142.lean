import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 142. -/
namespace Collatz.Research.RefinementAtlas.Batch142
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 22). -/
theorem data_9_22 : oddCount 22 9 = 4 ∧
    acceleratedOrbit 9 22 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_22 : gap 9 22 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_22 : threshold 9 22 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_22 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 22) = 81 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 22
  rw [data_9_22.1, data_9_22.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_22 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 22) = 81 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 22
  rw [data_9_22.1, data_9_22.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_22 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 22) < 512 * (2 * m) + 22 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 22 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_22] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 22) < 512 * (2 * m) + 22 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_22 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 22) < 512 * (2 * m + 1) + 22 := by
  apply refinement_cleared (k := 9) (r := 22) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_22]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 23). -/
theorem data_9_23 : oddCount 23 9 = 4 ∧
    acceleratedOrbit 9 23 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_23 : gap 9 23 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_23 : threshold 9 23 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_23 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 23) = 81 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 23
  rw [data_9_23.1, data_9_23.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_23 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 23) = 81 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 23
  rw [data_9_23.1, data_9_23.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_23 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 23) < 512 * (2 * m) + 23 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 23 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_23] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 23) < 512 * (2 * m) + 23 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_23 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 23) < 512 * (2 * m + 1) + 23 := by
  apply refinement_cleared (k := 9) (r := 23) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_23]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 24). -/
theorem data_9_24 : oddCount 24 9 = 3 ∧
    acceleratedOrbit 9 24 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_24 : gap 9 24 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_24 : threshold 9 24 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_24 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 24) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 24
  rw [data_9_24.1, data_9_24.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_24 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 24) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 24
  rw [data_9_24.1, data_9_24.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_24 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 24) < 512 * (2 * m) + 24 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 24 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_24] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 24) < 512 * (2 * m) + 24 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_24 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 24) < 512 * (2 * m + 1) + 24 := by
  apply refinement_cleared (k := 9) (r := 24) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_24]; decide

end Collatz.Research.RefinementAtlas.Batch142
