import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 153. -/
namespace Collatz.Research.RefinementAtlas.Batch153
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 61). -/
theorem data_9_61 : oddCount 61 9 = 4 ∧
    acceleratedOrbit 9 61 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_61 : gap 9 61 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_61 : threshold 9 61 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_61 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 61) = 81 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 61
  rw [data_9_61.1, data_9_61.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_61 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 61) = 81 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 61
  rw [data_9_61.1, data_9_61.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_61 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 61) < 512 * (2 * m) + 61 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 61 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_61] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 61) < 512 * (2 * m) + 61 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_61 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 61) < 512 * (2 * m + 1) + 61 := by
  apply refinement_cleared (k := 9) (r := 61) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_61]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 64). -/
theorem data_9_64 : oddCount 64 9 = 2 ∧
    acceleratedOrbit 9 64 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_64 : gap 9 64 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_64 : threshold 9 64 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_64 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 64) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 64
  rw [data_9_64.1, data_9_64.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_64 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 64) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 64
  rw [data_9_64.1, data_9_64.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_64 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 64) < 512 * (2 * m) + 64 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 64 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_64] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 64) < 512 * (2 * m) + 64 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_64 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 64) < 512 * (2 * m + 1) + 64 := by
  apply refinement_cleared (k := 9) (r := 64) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_64]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 65). -/
theorem data_9_65 : oddCount 65 9 = 4 ∧
    acceleratedOrbit 9 65 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_65 : gap 9 65 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_65 : threshold 9 65 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_65 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 65) = 81 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 65
  rw [data_9_65.1, data_9_65.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_65 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 65) = 81 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 65
  rw [data_9_65.1, data_9_65.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_65 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 65) < 512 * (2 * m) + 65 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 65 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_65] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 65) < 512 * (2 * m) + 65 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_65 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 65) < 512 * (2 * m + 1) + 65 := by
  apply refinement_cleared (k := 9) (r := 65) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_65]; decide

end Collatz.Research.RefinementAtlas.Batch153
