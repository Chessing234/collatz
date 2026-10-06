import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 057. -/
namespace Collatz.Research.RefinementAtlas.Batch057
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 90). -/
theorem data_7_90 : oddCount 90 7 = 3 ∧
    acceleratedOrbit 7 90 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_90 : gap 7 90 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_90 : threshold 7 90 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_90 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 90) = 27 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 90
  rw [data_7_90.1, data_7_90.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_90 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 90) = 27 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 90
  rw [data_7_90.1, data_7_90.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_90 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 90) < 128 * (2 * m) + 90 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 90 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_90] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 90) < 128 * (2 * m) + 90 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_90 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 90) < 128 * (2 * m + 1) + 90 := by
  apply refinement_cleared (k := 7) (r := 90) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_90]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 92). -/
theorem data_7_92 : oddCount 92 7 = 3 ∧
    acceleratedOrbit 7 92 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_92 : gap 7 92 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_92 : threshold 7 92 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_92 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 92) = 27 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 92
  rw [data_7_92.1, data_7_92.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_92 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 92) = 27 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 92
  rw [data_7_92.1, data_7_92.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_92 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 92) < 128 * (2 * m) + 92 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 92 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_92] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 92) < 128 * (2 * m) + 92 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_92 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 92) < 128 * (2 * m + 1) + 92 := by
  apply refinement_cleared (k := 7) (r := 92) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_92]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 93). -/
theorem data_7_93 : oddCount 93 7 = 3 ∧
    acceleratedOrbit 7 93 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_93 : gap 7 93 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_93 : threshold 7 93 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_93 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 93) = 27 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 93
  rw [data_7_93.1, data_7_93.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_93 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 93) = 27 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 93
  rw [data_7_93.1, data_7_93.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_93 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 93) < 128 * (2 * m) + 93 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 93 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_93] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 93) < 128 * (2 * m) + 93 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_93 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 93) < 128 * (2 * m + 1) + 93 := by
  apply refinement_cleared (k := 7) (r := 93) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_93]; decide

end Collatz.Research.RefinementAtlas.Batch057
