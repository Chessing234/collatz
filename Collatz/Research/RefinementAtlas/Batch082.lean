import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 082. -/
namespace Collatz.Research.RefinementAtlas.Batch082
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 67). -/
theorem data_8_67 : oddCount 67 8 = 4 ∧
    acceleratedOrbit 8 67 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_67 : gap 8 67 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_67 : threshold 8 67 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_67 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 67) = 81 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 67
  rw [data_8_67.1, data_8_67.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_67 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 67) = 81 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 67
  rw [data_8_67.1, data_8_67.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_67 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 67) < 256 * (2 * m) + 67 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 67 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_67] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 67) < 256 * (2 * m) + 67 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_67 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 67) < 256 * (2 * m + 1) + 67 := by
  apply refinement_cleared (k := 8) (r := 67) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_67]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 68). -/
theorem data_8_68 : oddCount 68 8 = 3 ∧
    acceleratedOrbit 8 68 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_68 : gap 8 68 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_68 : threshold 8 68 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_68 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 68) = 27 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 68
  rw [data_8_68.1, data_8_68.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_68 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 68) = 27 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 68
  rw [data_8_68.1, data_8_68.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_68 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 68) < 256 * (2 * m) + 68 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 68 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_68] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 68) < 256 * (2 * m) + 68 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_68 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 68) < 256 * (2 * m + 1) + 68 := by
  apply refinement_cleared (k := 8) (r := 68) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_68]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 69). -/
theorem data_8_69 : oddCount 69 8 = 3 ∧
    acceleratedOrbit 8 69 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_69 : gap 8 69 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_69 : threshold 8 69 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_69 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 69) = 27 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 69
  rw [data_8_69.1, data_8_69.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_69 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 69) = 27 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 69
  rw [data_8_69.1, data_8_69.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_69 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 69) < 256 * (2 * m) + 69 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 69 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_69] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 69) < 256 * (2 * m) + 69 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_69 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 69) < 256 * (2 * m + 1) + 69 := by
  apply refinement_cleared (k := 8) (r := 69) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_69]; decide

end Collatz.Research.RefinementAtlas.Batch082
