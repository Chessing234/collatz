import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 083. -/
namespace Collatz.Research.RefinementAtlas.Batch083
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 70). -/
theorem data_8_70 : oddCount 70 8 = 3 ∧
    acceleratedOrbit 8 70 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_70 : gap 8 70 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_70 : threshold 8 70 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_70 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 70) = 27 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 70
  rw [data_8_70.1, data_8_70.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_70 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 70) = 27 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 70
  rw [data_8_70.1, data_8_70.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_70 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 70) < 256 * (2 * m) + 70 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 70 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_70] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 70) < 256 * (2 * m) + 70 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_70 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 70) < 256 * (2 * m + 1) + 70 := by
  apply refinement_cleared (k := 8) (r := 70) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_70]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 72). -/
theorem data_8_72 : oddCount 72 8 = 4 ∧
    acceleratedOrbit 8 72 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_72 : gap 8 72 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_72 : threshold 8 72 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_72 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 72) = 81 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 72
  rw [data_8_72.1, data_8_72.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_72 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 72) = 81 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 72
  rw [data_8_72.1, data_8_72.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_72 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 72) < 256 * (2 * m) + 72 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 72 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_72] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 72) < 256 * (2 * m) + 72 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_72 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 72) < 256 * (2 * m + 1) + 72 := by
  apply refinement_cleared (k := 8) (r := 72) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_72]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 73). -/
theorem data_8_73 : oddCount 73 8 = 5 ∧
    acceleratedOrbit 8 73 = 71 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_73 : gap 8 73 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_73 : threshold 8 73 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_73 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 73) = 243 * (2 * m) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 73
  rw [data_8_73.1, data_8_73.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_73 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 73) = 243 * (2 * m + 1) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 73
  rw [data_8_73.1, data_8_73.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_73 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 73) < 256 * (2 * m) + 73 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 73 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_73] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 73) < 256 * (2 * m) + 73 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_73 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 73) < 256 * (2 * m + 1) + 73 := by
  apply refinement_cleared (k := 8) (r := 73) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_73]; decide

end Collatz.Research.RefinementAtlas.Batch083
