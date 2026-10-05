import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 154. -/
namespace Collatz.Research.RefinementAtlas.Batch154
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 66). -/
theorem data_9_66 : oddCount 66 9 = 4 ∧
    acceleratedOrbit 9 66 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_66 : gap 9 66 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_66 : threshold 9 66 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_66 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 66) = 81 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 66
  rw [data_9_66.1, data_9_66.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_66 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 66) = 81 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 66
  rw [data_9_66.1, data_9_66.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_66 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 66) < 512 * (2 * m) + 66 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 66 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_66] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 66) < 512 * (2 * m) + 66 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_66 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 66) < 512 * (2 * m + 1) + 66 := by
  apply refinement_cleared (k := 9) (r := 66) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_66]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 67). -/
theorem data_9_67 : oddCount 67 9 = 4 ∧
    acceleratedOrbit 9 67 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_67 : gap 9 67 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_67 : threshold 9 67 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_67 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 67) = 81 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 67
  rw [data_9_67.1, data_9_67.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_67 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 67) = 81 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 67
  rw [data_9_67.1, data_9_67.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_67 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 67) < 512 * (2 * m) + 67 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 67 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_67] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 67) < 512 * (2 * m) + 67 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_67 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 67) < 512 * (2 * m + 1) + 67 := by
  apply refinement_cleared (k := 9) (r := 67) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_67]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 68). -/
theorem data_9_68 : oddCount 68 9 = 3 ∧
    acceleratedOrbit 9 68 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_68 : gap 9 68 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_68 : threshold 9 68 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_68 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 68) = 27 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 68
  rw [data_9_68.1, data_9_68.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_68 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 68) = 27 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 68
  rw [data_9_68.1, data_9_68.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_68 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 68) < 512 * (2 * m) + 68 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 68 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_68] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 68) < 512 * (2 * m) + 68 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_68 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 68) < 512 * (2 * m + 1) + 68 := by
  apply refinement_cleared (k := 9) (r := 68) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_68]; decide

end Collatz.Research.RefinementAtlas.Batch154
