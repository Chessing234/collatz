import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 132. -/
namespace Collatz.Research.RefinementAtlas.Batch132
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 241). -/
theorem data_8_241 : oddCount 241 8 = 3 ∧
    acceleratedOrbit 8 241 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_241 : gap 8 241 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_241 : threshold 8 241 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_241 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 241) = 27 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 241
  rw [data_8_241.1, data_8_241.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_241 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 241) = 27 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 241
  rw [data_8_241.1, data_8_241.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_241 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 241) < 256 * (2 * m) + 241 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 241 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_241] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 241) < 256 * (2 * m) + 241 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_241 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 241) < 256 * (2 * m + 1) + 241 := by
  apply refinement_cleared (k := 8) (r := 241) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_241]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 242). -/
theorem data_8_242 : oddCount 242 8 = 5 ∧
    acceleratedOrbit 8 242 = 233 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_242 : gap 8 242 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_242 : threshold 8 242 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_242 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 242) = 243 * (2 * m) + 233 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 242
  rw [data_8_242.1, data_8_242.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_242 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 242) = 243 * (2 * m + 1) + 233 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 242
  rw [data_8_242.1, data_8_242.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_242 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 242) < 256 * (2 * m) + 242 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 242 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_242] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 242) < 256 * (2 * m) + 242 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_242 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 242) < 256 * (2 * m + 1) + 242 := by
  apply refinement_cleared (k := 8) (r := 242) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_242]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 243). -/
theorem data_8_243 : oddCount 243 8 = 5 ∧
    acceleratedOrbit 8 243 = 233 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_243 : gap 8 243 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_243 : threshold 8 243 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_243 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 243) = 243 * (2 * m) + 233 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 243
  rw [data_8_243.1, data_8_243.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_243 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 243) = 243 * (2 * m + 1) + 233 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 243
  rw [data_8_243.1, data_8_243.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_243 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 243) < 256 * (2 * m) + 243 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 243 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_243] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 243) < 256 * (2 * m) + 243 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_243 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 243) < 256 * (2 * m + 1) + 243 := by
  apply refinement_cleared (k := 8) (r := 243) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_243]; decide

end Collatz.Research.RefinementAtlas.Batch132
