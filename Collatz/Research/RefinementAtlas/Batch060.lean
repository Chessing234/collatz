import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 060. -/
namespace Collatz.Research.RefinementAtlas.Batch060
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 104). -/
theorem data_7_104 : oddCount 104 7 = 2 ∧
    acceleratedOrbit 7 104 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_104 : gap 7 104 = 119 ∧ 9 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_104 : threshold 7 104 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_104 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 104) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 104
  rw [data_7_104.1, data_7_104.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_104 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 104) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 104
  rw [data_7_104.1, data_7_104.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_104 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 104) < 128 * (2 * m) + 104 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 104 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_104] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 104) < 128 * (2 * m) + 104 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_104 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 104) < 128 * (2 * m + 1) + 104 := by
  apply refinement_cleared (k := 7) (r := 104) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_104]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 106). -/
theorem data_7_106 : oddCount 106 7 = 2 ∧
    acceleratedOrbit 7 106 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_106 : gap 7 106 = 119 ∧ 9 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_106 : threshold 7 106 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_106 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 106) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 106
  rw [data_7_106.1, data_7_106.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_106 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 106) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 106
  rw [data_7_106.1, data_7_106.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_106 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 106) < 128 * (2 * m) + 106 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 106 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_106] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 106) < 128 * (2 * m) + 106 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_106 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 106) < 128 * (2 * m + 1) + 106 := by
  apply refinement_cleared (k := 7) (r := 106) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_106]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 108). -/
theorem data_7_108 : oddCount 108 7 = 4 ∧
    acceleratedOrbit 7 108 = 71 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_108 : gap 7 108 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_108 : threshold 7 108 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_108 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 108) = 81 * (2 * m) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 108
  rw [data_7_108.1, data_7_108.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_108 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 108) = 81 * (2 * m + 1) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 108
  rw [data_7_108.1, data_7_108.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_108 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 108) < 128 * (2 * m) + 108 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 108 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_108] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 108) < 128 * (2 * m) + 108 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_108 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 108) < 128 * (2 * m + 1) + 108 := by
  apply refinement_cleared (k := 7) (r := 108) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_108]; decide

end Collatz.Research.RefinementAtlas.Batch060
