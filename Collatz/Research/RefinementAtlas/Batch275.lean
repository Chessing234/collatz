import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 275. -/
namespace Collatz.Research.RefinementAtlas.Batch275
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 45). -/
theorem data_10_45 : oddCount 45 10 = 4 ∧
    acceleratedOrbit 10 45 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_45 : gap 10 45 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_45 : threshold 10 45 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_45 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 45) = 81 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 45
  rw [data_10_45.1, data_10_45.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_45 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 45) = 81 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 45
  rw [data_10_45.1, data_10_45.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_45 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 45) < 1024 * (2 * m) + 45 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 45 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_45] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 45) < 1024 * (2 * m) + 45 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_45 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 45) < 1024 * (2 * m + 1) + 45 := by
  apply refinement_cleared (k := 10) (r := 45) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_45]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 46). -/
theorem data_10_46 : oddCount 46 10 = 4 ∧
    acceleratedOrbit 10 46 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_46 : gap 10 46 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_46 : threshold 10 46 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_46 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 46) = 81 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 46
  rw [data_10_46.1, data_10_46.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_46 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 46) = 81 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 46
  rw [data_10_46.1, data_10_46.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_46 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 46) < 1024 * (2 * m) + 46 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 46 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_46] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 46) < 1024 * (2 * m) + 46 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_46 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 46) < 1024 * (2 * m + 1) + 46 := by
  apply refinement_cleared (k := 10) (r := 46) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_46]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 48). -/
theorem data_10_48 : oddCount 48 10 = 3 ∧
    acceleratedOrbit 10 48 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_48 : gap 10 48 = 997 ∧ 27 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_48 : threshold 10 48 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_48 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 48) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 48
  rw [data_10_48.1, data_10_48.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_48 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 48) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 48
  rw [data_10_48.1, data_10_48.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_48 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 48) < 1024 * (2 * m) + 48 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 48 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_48] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 48) < 1024 * (2 * m) + 48 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_48 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 48) < 1024 * (2 * m + 1) + 48 := by
  apply refinement_cleared (k := 10) (r := 48) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_48]; decide

end Collatz.Research.RefinementAtlas.Batch275
