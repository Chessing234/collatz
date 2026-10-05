import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 118. -/
namespace Collatz.Research.RefinementAtlas.Batch118
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 189). -/
theorem data_8_189 : oddCount 189 8 = 5 ∧
    acceleratedOrbit 8 189 = 182 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_189 : gap 8 189 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_189 : threshold 8 189 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_189 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 189) = 243 * (2 * m) + 182 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 189
  rw [data_8_189.1, data_8_189.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_189 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 189) = 243 * (2 * m + 1) + 182 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 189
  rw [data_8_189.1, data_8_189.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_189 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 189) < 256 * (2 * m) + 189 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 189 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_189] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 189) < 256 * (2 * m) + 189 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_189 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 189) < 256 * (2 * m + 1) + 189 := by
  apply refinement_cleared (k := 8) (r := 189) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_189]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 190). -/
theorem data_8_190 : oddCount 190 8 = 5 ∧
    acceleratedOrbit 8 190 = 182 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_190 : gap 8 190 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_190 : threshold 8 190 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_190 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 190) = 243 * (2 * m) + 182 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 190
  rw [data_8_190.1, data_8_190.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_190 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 190) = 243 * (2 * m + 1) + 182 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 190
  rw [data_8_190.1, data_8_190.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_190 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 190) < 256 * (2 * m) + 190 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 190 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_190] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 190) < 256 * (2 * m) + 190 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_190 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 190) < 256 * (2 * m + 1) + 190 := by
  apply refinement_cleared (k := 8) (r := 190) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_190]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 192). -/
theorem data_8_192 : oddCount 192 8 = 2 ∧
    acceleratedOrbit 8 192 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_192 : gap 8 192 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_192 : threshold 8 192 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_192 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 192) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 192
  rw [data_8_192.1, data_8_192.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_192 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 192) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 192
  rw [data_8_192.1, data_8_192.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_192 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 192) < 256 * (2 * m) + 192 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 192 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_192] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 192) < 256 * (2 * m) + 192 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_192 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 192) < 256 * (2 * m + 1) + 192 := by
  apply refinement_cleared (k := 8) (r := 192) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_192]; decide

end Collatz.Research.RefinementAtlas.Batch118
