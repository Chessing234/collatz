import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 122. -/
namespace Collatz.Research.RefinementAtlas.Batch122
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 202). -/
theorem data_8_202 : oddCount 202 8 = 3 ∧
    acceleratedOrbit 8 202 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_202 : gap 8 202 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_202 : threshold 8 202 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_202 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 202) = 27 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 202
  rw [data_8_202.1, data_8_202.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_202 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 202) = 27 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 202
  rw [data_8_202.1, data_8_202.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_202 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 202) < 256 * (2 * m) + 202 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 202 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_202] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 202) < 256 * (2 * m) + 202 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_202 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 202) < 256 * (2 * m + 1) + 202 := by
  apply refinement_cleared (k := 8) (r := 202) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_202]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 203). -/
theorem data_8_203 : oddCount 203 8 = 4 ∧
    acceleratedOrbit 8 203 = 65 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_203 : gap 8 203 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_203 : threshold 8 203 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_203 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 203) = 81 * (2 * m) + 65 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 203
  rw [data_8_203.1, data_8_203.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_203 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 203) = 81 * (2 * m + 1) + 65 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 203
  rw [data_8_203.1, data_8_203.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_203 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 203) < 256 * (2 * m) + 203 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 203 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_203] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 203) < 256 * (2 * m) + 203 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_203 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 203) < 256 * (2 * m + 1) + 203 := by
  apply refinement_cleared (k := 8) (r := 203) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_203]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 204). -/
theorem data_8_204 : oddCount 204 8 = 3 ∧
    acceleratedOrbit 8 204 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_204 : gap 8 204 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_204 : threshold 8 204 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_204 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 204) = 27 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 204
  rw [data_8_204.1, data_8_204.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_204 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 204) = 27 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 204
  rw [data_8_204.1, data_8_204.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_204 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 204) < 256 * (2 * m) + 204 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 204 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_204] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 204) < 256 * (2 * m) + 204 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_204 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 204) < 256 * (2 * m + 1) + 204 := by
  apply refinement_cleared (k := 8) (r := 204) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_204]; decide

end Collatz.Research.RefinementAtlas.Batch122
