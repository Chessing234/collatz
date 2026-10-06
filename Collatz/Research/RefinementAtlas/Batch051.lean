import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 051. -/
namespace Collatz.Research.RefinementAtlas.Batch051
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 67). -/
theorem data_7_67 : oddCount 67 7 = 4 ∧
    acceleratedOrbit 7 67 = 44 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_67 : gap 7 67 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_67 : threshold 7 67 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_67 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 67) = 81 * (2 * m) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 67
  rw [data_7_67.1, data_7_67.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_67 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 67) = 81 * (2 * m + 1) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 67
  rw [data_7_67.1, data_7_67.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_67 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 67) < 128 * (2 * m) + 67 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 67 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_67] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 67) < 128 * (2 * m) + 67 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_67 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 67) < 128 * (2 * m + 1) + 67 := by
  apply refinement_cleared (k := 7) (r := 67) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_67]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 68). -/
theorem data_7_68 : oddCount 68 7 = 2 ∧
    acceleratedOrbit 7 68 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_68 : gap 7 68 = 119 ∧ 9 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_68 : threshold 7 68 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_68 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 68) = 9 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 68
  rw [data_7_68.1, data_7_68.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_68 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 68) = 9 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 68
  rw [data_7_68.1, data_7_68.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_68 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 68) < 128 * (2 * m) + 68 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 68 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_68] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 68) < 128 * (2 * m) + 68 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_68 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 68) < 128 * (2 * m + 1) + 68 := by
  apply refinement_cleared (k := 7) (r := 68) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_68]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 69). -/
theorem data_7_69 : oddCount 69 7 = 2 ∧
    acceleratedOrbit 7 69 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_69 : gap 7 69 = 119 ∧ 9 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_69 : threshold 7 69 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_69 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 69) = 9 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 69
  rw [data_7_69.1, data_7_69.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_69 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 69) = 9 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 69
  rw [data_7_69.1, data_7_69.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_69 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 69) < 128 * (2 * m) + 69 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 69 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_69] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 69) < 128 * (2 * m) + 69 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_69 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 69) < 128 * (2 * m + 1) + 69 := by
  apply refinement_cleared (k := 7) (r := 69) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_69]; decide

end Collatz.Research.RefinementAtlas.Batch051
