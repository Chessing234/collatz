import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 093. -/
namespace Collatz.Research.RefinementAtlas.Batch093
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 105). -/
theorem data_8_105 : oddCount 105 8 = 5 ∧
    acceleratedOrbit 8 105 = 101 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_105 : gap 8 105 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_105 : threshold 8 105 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_105 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 105) = 243 * (2 * m) + 101 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 105
  rw [data_8_105.1, data_8_105.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_105 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 105) = 243 * (2 * m + 1) + 101 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 105
  rw [data_8_105.1, data_8_105.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_105 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 105) < 256 * (2 * m) + 105 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 105 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_105] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 105) < 256 * (2 * m) + 105 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_105 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 105) < 256 * (2 * m + 1) + 105 := by
  apply refinement_cleared (k := 8) (r := 105) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_105]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 106). -/
theorem data_8_106 : oddCount 106 8 = 2 ∧
    acceleratedOrbit 8 106 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_106 : gap 8 106 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_106 : threshold 8 106 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_106 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 106) = 9 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 106
  rw [data_8_106.1, data_8_106.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_106 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 106) = 9 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 106
  rw [data_8_106.1, data_8_106.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_106 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 106) < 256 * (2 * m) + 106 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 106 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_106] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 106) < 256 * (2 * m) + 106 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_106 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 106) < 256 * (2 * m + 1) + 106 := by
  apply refinement_cleared (k := 8) (r := 106) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_106]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 107). -/
theorem data_8_107 : oddCount 107 8 = 5 ∧
    acceleratedOrbit 8 107 = 103 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_107 : gap 8 107 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_107 : threshold 8 107 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_107 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 107) = 243 * (2 * m) + 103 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 107
  rw [data_8_107.1, data_8_107.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_107 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 107) = 243 * (2 * m + 1) + 103 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 107
  rw [data_8_107.1, data_8_107.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_107 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 107) < 256 * (2 * m) + 107 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 107 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_107] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 107) < 256 * (2 * m) + 107 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_107 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 107) < 256 * (2 * m + 1) + 107 := by
  apply refinement_cleared (k := 8) (r := 107) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_107]; decide

end Collatz.Research.RefinementAtlas.Batch093
