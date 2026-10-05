import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 115. -/
namespace Collatz.Research.RefinementAtlas.Batch115
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 180). -/
theorem data_8_180 : oddCount 180 8 = 3 ∧
    acceleratedOrbit 8 180 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_180 : gap 8 180 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_180 : threshold 8 180 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_180 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 180) = 27 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 180
  rw [data_8_180.1, data_8_180.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_180 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 180) = 27 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 180
  rw [data_8_180.1, data_8_180.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_180 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 180) < 256 * (2 * m) + 180 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 180 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_180] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 180) < 256 * (2 * m) + 180 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_180 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 180) < 256 * (2 * m + 1) + 180 := by
  apply refinement_cleared (k := 8) (r := 180) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_180]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 181). -/
theorem data_8_181 : oddCount 181 8 = 3 ∧
    acceleratedOrbit 8 181 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_181 : gap 8 181 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_181 : threshold 8 181 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_181 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 181) = 27 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 181
  rw [data_8_181.1, data_8_181.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_181 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 181) = 27 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 181
  rw [data_8_181.1, data_8_181.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_181 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 181) < 256 * (2 * m) + 181 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 181 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_181] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 181) < 256 * (2 * m) + 181 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_181 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 181) < 256 * (2 * m + 1) + 181 := by
  apply refinement_cleared (k := 8) (r := 181) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_181]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 182). -/
theorem data_8_182 : oddCount 182 8 = 5 ∧
    acceleratedOrbit 8 182 = 175 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_182 : gap 8 182 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_182 : threshold 8 182 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_182 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 182) = 243 * (2 * m) + 175 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 182
  rw [data_8_182.1, data_8_182.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_182 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 182) = 243 * (2 * m + 1) + 175 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 182
  rw [data_8_182.1, data_8_182.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_182 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 182) < 256 * (2 * m) + 182 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 182 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_182] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 182) < 256 * (2 * m) + 182 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_182 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 182) < 256 * (2 * m + 1) + 182 := by
  apply refinement_cleared (k := 8) (r := 182) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_182]; decide

end Collatz.Research.RefinementAtlas.Batch115
