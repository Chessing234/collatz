import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 131. -/
namespace Collatz.Research.RefinementAtlas.Batch131
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 237). -/
theorem data_8_237 : oddCount 237 8 = 4 ∧
    acceleratedOrbit 8 237 = 76 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_237 : gap 8 237 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_237 : threshold 8 237 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_237 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 237) = 81 * (2 * m) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 237
  rw [data_8_237.1, data_8_237.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_237 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 237) = 81 * (2 * m + 1) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 237
  rw [data_8_237.1, data_8_237.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_237 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 237) < 256 * (2 * m) + 237 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 237 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_237] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 237) < 256 * (2 * m) + 237 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_237 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 237) < 256 * (2 * m + 1) + 237 := by
  apply refinement_cleared (k := 8) (r := 237) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_237]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 238). -/
theorem data_8_238 : oddCount 238 8 = 4 ∧
    acceleratedOrbit 8 238 = 76 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_238 : gap 8 238 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_238 : threshold 8 238 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_238 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 238) = 81 * (2 * m) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 238
  rw [data_8_238.1, data_8_238.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_238 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 238) = 81 * (2 * m + 1) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 238
  rw [data_8_238.1, data_8_238.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_238 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 238) < 256 * (2 * m) + 238 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 238 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_238] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 238) < 256 * (2 * m) + 238 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_238 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 238) < 256 * (2 * m + 1) + 238 := by
  apply refinement_cleared (k := 8) (r := 238) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_238]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 240). -/
theorem data_8_240 : oddCount 240 8 = 4 ∧
    acceleratedOrbit 8 240 = 80 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_240 : gap 8 240 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_240 : threshold 8 240 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_240 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 240) = 81 * (2 * m) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 240
  rw [data_8_240.1, data_8_240.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_240 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 240) = 81 * (2 * m + 1) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 240
  rw [data_8_240.1, data_8_240.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_240 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 240) < 256 * (2 * m) + 240 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 240 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_240] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 240) < 256 * (2 * m) + 240 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_240 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 240) < 256 * (2 * m + 1) + 240 := by
  apply refinement_cleared (k := 8) (r := 240) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_240]; decide

end Collatz.Research.RefinementAtlas.Batch131
