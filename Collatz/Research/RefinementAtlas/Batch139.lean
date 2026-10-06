import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 139. -/
namespace Collatz.Research.RefinementAtlas.Batch139
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 13). -/
theorem data_9_13 : oddCount 13 9 = 3 ∧
    acceleratedOrbit 9 13 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_13 : gap 9 13 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_13 : threshold 9 13 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_13 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 13) = 27 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 13
  rw [data_9_13.1, data_9_13.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_13 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 13) = 27 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 13
  rw [data_9_13.1, data_9_13.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_13 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 13) < 512 * (2 * m) + 13 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 13 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_13] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 13) < 512 * (2 * m) + 13 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_13 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 13) < 512 * (2 * m + 1) + 13 := by
  apply refinement_cleared (k := 9) (r := 13) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_13]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 14). -/
theorem data_9_14 : oddCount 14 9 = 5 ∧
    acceleratedOrbit 9 14 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_14 : gap 9 14 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_14 : threshold 9 14 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_14 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 14) = 243 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 14
  rw [data_9_14.1, data_9_14.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_14 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 14) = 243 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 14
  rw [data_9_14.1, data_9_14.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_14 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 14) < 512 * (2 * m) + 14 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 14 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_14] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 14) < 512 * (2 * m) + 14 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_14 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 14) < 512 * (2 * m + 1) + 14 := by
  apply refinement_cleared (k := 9) (r := 14) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_14]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 15). -/
theorem data_9_15 : oddCount 15 9 = 5 ∧
    acceleratedOrbit 9 15 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_15 : gap 9 15 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_15 : threshold 9 15 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_15 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 15) = 243 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 15
  rw [data_9_15.1, data_9_15.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_15 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 15) = 243 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 15
  rw [data_9_15.1, data_9_15.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_15 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 15) < 512 * (2 * m) + 15 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 15 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_15] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 15) < 512 * (2 * m) + 15 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_15 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 15) < 512 * (2 * m + 1) + 15 := by
  apply refinement_cleared (k := 9) (r := 15) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_15]; decide

end Collatz.Research.RefinementAtlas.Batch139
