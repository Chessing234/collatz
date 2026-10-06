import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 045. -/
namespace Collatz.Research.RefinementAtlas.Batch045
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 44). -/
theorem data_7_44 : oddCount 44 7 = 3 ∧
    acceleratedOrbit 7 44 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_44 : gap 7 44 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_44 : threshold 7 44 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_44 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 44) = 27 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 44
  rw [data_7_44.1, data_7_44.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_44 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 44) = 27 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 44
  rw [data_7_44.1, data_7_44.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_44 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 44) < 128 * (2 * m) + 44 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 44 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_44] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 44) < 128 * (2 * m) + 44 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_44 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 44) < 128 * (2 * m + 1) + 44 := by
  apply refinement_cleared (k := 7) (r := 44) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_44]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 45). -/
theorem data_7_45 : oddCount 45 7 = 3 ∧
    acceleratedOrbit 7 45 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_45 : gap 7 45 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_45 : threshold 7 45 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_45 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 45) = 27 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 45
  rw [data_7_45.1, data_7_45.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_45 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 45) = 27 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 45
  rw [data_7_45.1, data_7_45.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_45 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 45) < 128 * (2 * m) + 45 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 45 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_45] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 45) < 128 * (2 * m) + 45 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_45 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 45) < 128 * (2 * m + 1) + 45 := by
  apply refinement_cleared (k := 7) (r := 45) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_45]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 46). -/
theorem data_7_46 : oddCount 46 7 = 3 ∧
    acceleratedOrbit 7 46 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_46 : gap 7 46 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_46 : threshold 7 46 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_46 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 46) = 27 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 46
  rw [data_7_46.1, data_7_46.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_46 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 46) = 27 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 46
  rw [data_7_46.1, data_7_46.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_46 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 46) < 128 * (2 * m) + 46 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 46 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_46] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 46) < 128 * (2 * m) + 46 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_46 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 46) < 128 * (2 * m + 1) + 46 := by
  apply refinement_cleared (k := 7) (r := 46) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_46]; decide

end Collatz.Research.RefinementAtlas.Batch045
