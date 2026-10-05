import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 005. -/
namespace Collatz.Research.RefinementAtlas.Batch005
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 18). -/
theorem data_8_18 : oddCount 18 8 = 5 ∧
    acceleratedOrbit 8 18 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_18 : gap 8 18 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_18 : threshold 8 18 = 1 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_18 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 18) = 243 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 18
  rw [data_8_18.1, data_8_18.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_18 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 18) = 243 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 18
  rw [data_8_18.1, data_8_18.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_18 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 18) < 256 * (2 * m) + 18 ↔ 1 ≤ m := by
  have hc : 3 ^ oddCount 18 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_18] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 18) < 256 * (2 * m) + 18 ↔ 1 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_18 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 18) < 256 * (2 * m + 1) + 18 := by
  apply refinement_cleared (k := 8) (r := 18) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_18]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 19). -/
theorem data_8_19 : oddCount 19 8 = 5 ∧
    acceleratedOrbit 8 19 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_19 : gap 8 19 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_19 : threshold 8 19 = 1 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_19 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 19) = 243 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 19
  rw [data_8_19.1, data_8_19.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_19 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 19) = 243 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 19
  rw [data_8_19.1, data_8_19.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_19 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 19) < 256 * (2 * m) + 19 ↔ 1 ≤ m := by
  have hc : 3 ^ oddCount 19 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_19] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 19) < 256 * (2 * m) + 19 ↔ 1 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_19 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 19) < 256 * (2 * m + 1) + 19 := by
  apply refinement_cleared (k := 8) (r := 19) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_19]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 25). -/
theorem data_8_25 : oddCount 25 8 = 5 ∧
    acceleratedOrbit 8 25 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_25 : gap 8 25 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_25 : threshold 8 25 = 1 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_25 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 25) = 243 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 25
  rw [data_8_25.1, data_8_25.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_25 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 25) = 243 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 25
  rw [data_8_25.1, data_8_25.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_25 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 25) < 256 * (2 * m) + 25 ↔ 1 ≤ m := by
  have hc : 3 ^ oddCount 25 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_25] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 25) < 256 * (2 * m) + 25 ↔ 1 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_25 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 25) < 256 * (2 * m + 1) + 25 := by
  apply refinement_cleared (k := 8) (r := 25) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_25]; decide

end Collatz.Research.RefinementAtlas.Batch005
