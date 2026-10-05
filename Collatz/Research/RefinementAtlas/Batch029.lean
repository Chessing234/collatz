import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 029. -/
namespace Collatz.Research.RefinementAtlas.Batch029
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (6, 44). -/
theorem data_6_44 : oddCount 44 6 = 3 ∧
    acceleratedOrbit 6 44 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_44 : gap 6 44 = 37 ∧ 27 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_44 : threshold 6 44 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_44 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 44) = 27 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 44
  rw [data_6_44.1, data_6_44.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_44 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 44) = 27 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 44
  rw [data_6_44.1, data_6_44.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_44 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 44) < 64 * (2 * m) + 44 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 44 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_44] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 44) < 64 * (2 * m) + 44 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_44 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 44) < 64 * (2 * m + 1) + 44 := by
  apply refinement_cleared (k := 6) (r := 44) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_44]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 45). -/
theorem data_6_45 : oddCount 45 6 = 3 ∧
    acceleratedOrbit 6 45 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_45 : gap 6 45 = 37 ∧ 27 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_45 : threshold 6 45 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_45 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 45) = 27 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 45
  rw [data_6_45.1, data_6_45.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_45 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 45) = 27 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 45
  rw [data_6_45.1, data_6_45.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_45 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 45) < 64 * (2 * m) + 45 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 45 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_45] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 45) < 64 * (2 * m) + 45 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_45 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 45) < 64 * (2 * m + 1) + 45 := by
  apply refinement_cleared (k := 6) (r := 45) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_45]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 46). -/
theorem data_6_46 : oddCount 46 6 = 3 ∧
    acceleratedOrbit 6 46 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_46 : gap 6 46 = 37 ∧ 27 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_46 : threshold 6 46 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_46 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 46) = 27 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 46
  rw [data_6_46.1, data_6_46.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_46 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 46) = 27 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 46
  rw [data_6_46.1, data_6_46.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_46 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 46) < 64 * (2 * m) + 46 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 46 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_46] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 46) < 64 * (2 * m) + 46 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_46 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 46) < 64 * (2 * m + 1) + 46 := by
  apply refinement_cleared (k := 6) (r := 46) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_46]; decide

end Collatz.Research.RefinementAtlas.Batch029
