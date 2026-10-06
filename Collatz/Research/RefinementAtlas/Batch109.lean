import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 109. -/
namespace Collatz.Research.RefinementAtlas.Batch109
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 160). -/
theorem data_8_160 : oddCount 160 8 = 1 ∧
    acceleratedOrbit 8 160 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_160 : gap 8 160 = 253 ∧ 3 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_160 : threshold 8 160 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_160 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 160) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 160
  rw [data_8_160.1, data_8_160.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_160 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 160) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 160
  rw [data_8_160.1, data_8_160.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_160 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 160) < 256 * (2 * m) + 160 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 160 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_160] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 160) < 256 * (2 * m) + 160 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_160 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 160) < 256 * (2 * m + 1) + 160 := by
  apply refinement_cleared (k := 8) (r := 160) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_160]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 161). -/
theorem data_8_161 : oddCount 161 8 = 5 ∧
    acceleratedOrbit 8 161 = 155 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_161 : gap 8 161 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_161 : threshold 8 161 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_161 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 161) = 243 * (2 * m) + 155 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 161
  rw [data_8_161.1, data_8_161.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_161 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 161) = 243 * (2 * m + 1) + 155 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 161
  rw [data_8_161.1, data_8_161.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_161 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 161) < 256 * (2 * m) + 161 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 161 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_161] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 161) < 256 * (2 * m) + 161 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_161 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 161) < 256 * (2 * m + 1) + 161 := by
  apply refinement_cleared (k := 8) (r := 161) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_161]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 162). -/
theorem data_8_162 : oddCount 162 8 = 4 ∧
    acceleratedOrbit 8 162 = 53 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_162 : gap 8 162 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_162 : threshold 8 162 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_162 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 162) = 81 * (2 * m) + 53 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 162
  rw [data_8_162.1, data_8_162.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_162 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 162) = 81 * (2 * m + 1) + 53 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 162
  rw [data_8_162.1, data_8_162.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_162 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 162) < 256 * (2 * m) + 162 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 162 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_162] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 162) < 256 * (2 * m) + 162 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_162 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 162) < 256 * (2 * m + 1) + 162 := by
  apply refinement_cleared (k := 8) (r := 162) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_162]; decide

end Collatz.Research.RefinementAtlas.Batch109
