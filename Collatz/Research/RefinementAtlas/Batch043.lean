import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 043. -/
namespace Collatz.Research.RefinementAtlas.Batch043
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 36). -/
theorem data_7_36 : oddCount 36 7 = 4 ∧
    acceleratedOrbit 7 36 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_36 : gap 7 36 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_36 : threshold 7 36 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_36 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 36) = 81 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 36
  rw [data_7_36.1, data_7_36.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_36 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 36) = 81 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 36
  rw [data_7_36.1, data_7_36.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_36 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 36) < 128 * (2 * m) + 36 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 36 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_36] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 36) < 128 * (2 * m) + 36 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_36 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 36) < 128 * (2 * m + 1) + 36 := by
  apply refinement_cleared (k := 7) (r := 36) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_36]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 37). -/
theorem data_7_37 : oddCount 37 7 = 4 ∧
    acceleratedOrbit 7 37 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_37 : gap 7 37 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_37 : threshold 7 37 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_37 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 37) = 81 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 37
  rw [data_7_37.1, data_7_37.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_37 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 37) = 81 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 37
  rw [data_7_37.1, data_7_37.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_37 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 37) < 128 * (2 * m) + 37 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 37 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_37] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 37) < 128 * (2 * m) + 37 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_37 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 37) < 128 * (2 * m + 1) + 37 := by
  apply refinement_cleared (k := 7) (r := 37) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_37]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 38). -/
theorem data_7_38 : oddCount 38 7 = 4 ∧
    acceleratedOrbit 7 38 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_38 : gap 7 38 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_38 : threshold 7 38 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_38 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 38) = 81 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 38
  rw [data_7_38.1, data_7_38.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_38 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 38) = 81 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 38
  rw [data_7_38.1, data_7_38.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_38 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 38) < 128 * (2 * m) + 38 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 38 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_38] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 38) < 128 * (2 * m) + 38 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_38 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 38) < 128 * (2 * m + 1) + 38 := by
  apply refinement_cleared (k := 7) (r := 38) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_38]; decide

end Collatz.Research.RefinementAtlas.Batch043
