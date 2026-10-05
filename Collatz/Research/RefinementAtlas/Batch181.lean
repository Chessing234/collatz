import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 181. -/
namespace Collatz.Research.RefinementAtlas.Batch181
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 179). -/
theorem data_9_179 : oddCount 179 9 = 4 ∧
    acceleratedOrbit 9 179 = 29 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_179 : gap 9 179 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_179 : threshold 9 179 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_179 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 179) = 81 * (2 * m) + 29 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 179
  rw [data_9_179.1, data_9_179.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_179 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 179) = 81 * (2 * m + 1) + 29 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 179
  rw [data_9_179.1, data_9_179.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_179 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 179) < 512 * (2 * m) + 179 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 179 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_179] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 179) < 512 * (2 * m) + 179 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_179 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 179) < 512 * (2 * m + 1) + 179 := by
  apply refinement_cleared (k := 9) (r := 179) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_179]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 180). -/
theorem data_9_180 : oddCount 180 9 = 3 ∧
    acceleratedOrbit 9 180 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_180 : gap 9 180 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_180 : threshold 9 180 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_180 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 180) = 27 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 180
  rw [data_9_180.1, data_9_180.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_180 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 180) = 27 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 180
  rw [data_9_180.1, data_9_180.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_180 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 180) < 512 * (2 * m) + 180 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 180 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_180] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 180) < 512 * (2 * m) + 180 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_180 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 180) < 512 * (2 * m + 1) + 180 := by
  apply refinement_cleared (k := 9) (r := 180) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_180]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 181). -/
theorem data_9_181 : oddCount 181 9 = 3 ∧
    acceleratedOrbit 9 181 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_181 : gap 9 181 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_181 : threshold 9 181 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_181 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 181) = 27 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 181
  rw [data_9_181.1, data_9_181.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_181 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 181) = 27 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 181
  rw [data_9_181.1, data_9_181.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_181 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 181) < 512 * (2 * m) + 181 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 181 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_181] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 181) < 512 * (2 * m) + 181 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_181 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 181) < 512 * (2 * m + 1) + 181 := by
  apply refinement_cleared (k := 9) (r := 181) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_181]; decide

end Collatz.Research.RefinementAtlas.Batch181
