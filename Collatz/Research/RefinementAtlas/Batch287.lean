import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 287. -/
namespace Collatz.Research.RefinementAtlas.Batch287
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 90). -/
theorem data_10_90 : oddCount 90 10 = 4 ∧
    acceleratedOrbit 10 90 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_90 : gap 10 90 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_90 : threshold 10 90 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_90 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 90) = 81 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 90
  rw [data_10_90.1, data_10_90.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_90 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 90) = 81 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 90
  rw [data_10_90.1, data_10_90.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_90 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 90) < 1024 * (2 * m) + 90 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 90 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_90] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 90) < 1024 * (2 * m) + 90 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_90 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 90) < 1024 * (2 * m + 1) + 90 := by
  apply refinement_cleared (k := 10) (r := 90) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_90]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 92). -/
theorem data_10_92 : oddCount 92 10 = 4 ∧
    acceleratedOrbit 10 92 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_92 : gap 10 92 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_92 : threshold 10 92 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_92 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 92) = 81 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 92
  rw [data_10_92.1, data_10_92.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_92 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 92) = 81 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 92
  rw [data_10_92.1, data_10_92.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_92 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 92) < 1024 * (2 * m) + 92 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 92 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_92] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 92) < 1024 * (2 * m) + 92 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_92 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 92) < 1024 * (2 * m + 1) + 92 := by
  apply refinement_cleared (k := 10) (r := 92) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_92]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 93). -/
theorem data_10_93 : oddCount 93 10 = 4 ∧
    acceleratedOrbit 10 93 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_93 : gap 10 93 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_93 : threshold 10 93 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_93 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 93) = 81 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 93
  rw [data_10_93.1, data_10_93.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_93 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 93) = 81 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 93
  rw [data_10_93.1, data_10_93.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_93 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 93) < 1024 * (2 * m) + 93 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 93 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_93] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 93) < 1024 * (2 * m) + 93 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_93 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 93) < 1024 * (2 * m + 1) + 93 := by
  apply refinement_cleared (k := 10) (r := 93) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_93]; decide

end Collatz.Research.RefinementAtlas.Batch287
