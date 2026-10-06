import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 056. -/
namespace Collatz.Research.RefinementAtlas.Batch056
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 87). -/
theorem data_7_87 : oddCount 87 7 = 4 ∧
    acceleratedOrbit 7 87 = 56 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_87 : gap 7 87 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_87 : threshold 7 87 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_87 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 87) = 81 * (2 * m) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 87
  rw [data_7_87.1, data_7_87.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_87 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 87) = 81 * (2 * m + 1) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 87
  rw [data_7_87.1, data_7_87.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_87 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 87) < 128 * (2 * m) + 87 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 87 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_87] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 87) < 128 * (2 * m) + 87 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_87 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 87) < 128 * (2 * m + 1) + 87 := by
  apply refinement_cleared (k := 7) (r := 87) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_87]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 88). -/
theorem data_7_88 : oddCount 88 7 = 3 ∧
    acceleratedOrbit 7 88 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_88 : gap 7 88 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_88 : threshold 7 88 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_88 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 88) = 27 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 88
  rw [data_7_88.1, data_7_88.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_88 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 88) = 27 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 88
  rw [data_7_88.1, data_7_88.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_88 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 88) < 128 * (2 * m) + 88 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 88 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_88] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 88) < 128 * (2 * m) + 88 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_88 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 88) < 128 * (2 * m + 1) + 88 := by
  apply refinement_cleared (k := 7) (r := 88) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_88]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 89). -/
theorem data_7_89 : oddCount 89 7 = 3 ∧
    acceleratedOrbit 7 89 = 19 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_89 : gap 7 89 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_89 : threshold 7 89 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_89 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 89) = 27 * (2 * m) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 89
  rw [data_7_89.1, data_7_89.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_89 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 89) = 27 * (2 * m + 1) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 89
  rw [data_7_89.1, data_7_89.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_89 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 89) < 128 * (2 * m) + 89 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 89 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_89] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 89) < 128 * (2 * m) + 89 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_89 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 89) < 128 * (2 * m + 1) + 89 := by
  apply refinement_cleared (k := 7) (r := 89) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_89]; decide

end Collatz.Research.RefinementAtlas.Batch056
