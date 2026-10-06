import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 076. -/
namespace Collatz.Research.RefinementAtlas.Batch076
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 44). -/
theorem data_8_44 : oddCount 44 8 = 3 ∧
    acceleratedOrbit 8 44 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_44 : gap 8 44 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_44 : threshold 8 44 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_44 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 44) = 27 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 44
  rw [data_8_44.1, data_8_44.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_44 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 44) = 27 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 44
  rw [data_8_44.1, data_8_44.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_44 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 44) < 256 * (2 * m) + 44 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 44 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_44] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 44) < 256 * (2 * m) + 44 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_44 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 44) < 256 * (2 * m + 1) + 44 := by
  apply refinement_cleared (k := 8) (r := 44) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_44]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 45). -/
theorem data_8_45 : oddCount 45 8 = 3 ∧
    acceleratedOrbit 8 45 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_45 : gap 8 45 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_45 : threshold 8 45 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_45 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 45) = 27 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 45
  rw [data_8_45.1, data_8_45.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_45 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 45) = 27 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 45
  rw [data_8_45.1, data_8_45.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_45 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 45) < 256 * (2 * m) + 45 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 45 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_45] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 45) < 256 * (2 * m) + 45 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_45 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 45) < 256 * (2 * m + 1) + 45 := by
  apply refinement_cleared (k := 8) (r := 45) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_45]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 46). -/
theorem data_8_46 : oddCount 46 8 = 3 ∧
    acceleratedOrbit 8 46 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_46 : gap 8 46 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_46 : threshold 8 46 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_46 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 46) = 27 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 46
  rw [data_8_46.1, data_8_46.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_46 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 46) = 27 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 46
  rw [data_8_46.1, data_8_46.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_46 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 46) < 256 * (2 * m) + 46 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 46 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_46] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 46) < 256 * (2 * m) + 46 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_46 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 46) < 256 * (2 * m + 1) + 46 := by
  apply refinement_cleared (k := 8) (r := 46) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_46]; decide

end Collatz.Research.RefinementAtlas.Batch076
