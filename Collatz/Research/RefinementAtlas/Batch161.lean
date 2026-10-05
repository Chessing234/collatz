import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 161. -/
namespace Collatz.Research.RefinementAtlas.Batch161
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 92). -/
theorem data_9_92 : oddCount 92 9 = 3 ∧
    acceleratedOrbit 9 92 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_92 : gap 9 92 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_92 : threshold 9 92 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_92 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 92) = 27 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 92
  rw [data_9_92.1, data_9_92.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_92 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 92) = 27 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 92
  rw [data_9_92.1, data_9_92.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_92 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 92) < 512 * (2 * m) + 92 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 92 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_92] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 92) < 512 * (2 * m) + 92 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_92 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 92) < 512 * (2 * m + 1) + 92 := by
  apply refinement_cleared (k := 9) (r := 92) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_92]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 93). -/
theorem data_9_93 : oddCount 93 9 = 3 ∧
    acceleratedOrbit 9 93 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_93 : gap 9 93 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_93 : threshold 9 93 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_93 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 93) = 27 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 93
  rw [data_9_93.1, data_9_93.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_93 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 93) = 27 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 93
  rw [data_9_93.1, data_9_93.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_93 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 93) < 512 * (2 * m) + 93 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 93 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_93] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 93) < 512 * (2 * m) + 93 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_93 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 93) < 512 * (2 * m + 1) + 93 := by
  apply refinement_cleared (k := 9) (r := 93) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_93]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 96). -/
theorem data_9_96 : oddCount 96 9 = 2 ∧
    acceleratedOrbit 9 96 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_96 : gap 9 96 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_96 : threshold 9 96 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_96 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 96) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 96
  rw [data_9_96.1, data_9_96.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_96 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 96) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 96
  rw [data_9_96.1, data_9_96.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_96 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 96) < 512 * (2 * m) + 96 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 96 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_96] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 96) < 512 * (2 * m) + 96 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_96 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 96) < 512 * (2 * m + 1) + 96 := by
  apply refinement_cleared (k := 9) (r := 96) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_96]; decide

end Collatz.Research.RefinementAtlas.Batch161
