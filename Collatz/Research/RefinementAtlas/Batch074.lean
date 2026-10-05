import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 074. -/
namespace Collatz.Research.RefinementAtlas.Batch074
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 37). -/
theorem data_8_37 : oddCount 37 8 = 4 ∧
    acceleratedOrbit 8 37 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_37 : gap 8 37 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_37 : threshold 8 37 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_37 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 37) = 81 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 37
  rw [data_8_37.1, data_8_37.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_37 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 37) = 81 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 37
  rw [data_8_37.1, data_8_37.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_37 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 37) < 256 * (2 * m) + 37 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 37 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_37] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 37) < 256 * (2 * m) + 37 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_37 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 37) < 256 * (2 * m + 1) + 37 := by
  apply refinement_cleared (k := 8) (r := 37) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_37]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 38). -/
theorem data_8_38 : oddCount 38 8 = 4 ∧
    acceleratedOrbit 8 38 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_38 : gap 8 38 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_38 : threshold 8 38 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_38 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 38) = 81 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 38
  rw [data_8_38.1, data_8_38.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_38 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 38) = 81 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 38
  rw [data_8_38.1, data_8_38.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_38 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 38) < 256 * (2 * m) + 38 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 38 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_38] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 38) < 256 * (2 * m) + 38 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_38 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 38) < 256 * (2 * m + 1) + 38 := by
  apply refinement_cleared (k := 8) (r := 38) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_38]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 39). -/
theorem data_8_39 : oddCount 39 8 = 5 ∧
    acceleratedOrbit 8 39 = 38 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_39 : gap 8 39 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_39 : threshold 8 39 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_39 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 39) = 243 * (2 * m) + 38 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 39
  rw [data_8_39.1, data_8_39.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_39 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 39) = 243 * (2 * m + 1) + 38 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 39
  rw [data_8_39.1, data_8_39.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_39 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 39) < 256 * (2 * m) + 39 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 39 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_39] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 39) < 256 * (2 * m) + 39 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_39 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 39) < 256 * (2 * m + 1) + 39 := by
  apply refinement_cleared (k := 8) (r := 39) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_39]; decide

end Collatz.Research.RefinementAtlas.Batch074
