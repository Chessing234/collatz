import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 166. -/
namespace Collatz.Research.RefinementAtlas.Batch166
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 116). -/
theorem data_9_116 : oddCount 116 9 = 4 ∧
    acceleratedOrbit 9 116 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_116 : gap 9 116 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_116 : threshold 9 116 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_116 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 116) = 81 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 116
  rw [data_9_116.1, data_9_116.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_116 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 116) = 81 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 116
  rw [data_9_116.1, data_9_116.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_116 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 116) < 512 * (2 * m) + 116 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 116 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_116] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 116) < 512 * (2 * m) + 116 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_116 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 116) < 512 * (2 * m + 1) + 116 := by
  apply refinement_cleared (k := 9) (r := 116) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_116]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 117). -/
theorem data_9_117 : oddCount 117 9 = 4 ∧
    acceleratedOrbit 9 117 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_117 : gap 9 117 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_117 : threshold 9 117 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_117 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 117) = 81 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 117
  rw [data_9_117.1, data_9_117.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_117 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 117) = 81 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 117
  rw [data_9_117.1, data_9_117.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_117 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 117) < 512 * (2 * m) + 117 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 117 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_117] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 117) < 512 * (2 * m) + 117 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_117 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 117) < 512 * (2 * m + 1) + 117 := by
  apply refinement_cleared (k := 9) (r := 117) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_117]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 118). -/
theorem data_9_118 : oddCount 118 9 = 4 ∧
    acceleratedOrbit 9 118 = 19 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_118 : gap 9 118 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_118 : threshold 9 118 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_118 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 118) = 81 * (2 * m) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 118
  rw [data_9_118.1, data_9_118.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_118 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 118) = 81 * (2 * m + 1) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 118
  rw [data_9_118.1, data_9_118.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_118 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 118) < 512 * (2 * m) + 118 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 118 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_118] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 118) < 512 * (2 * m) + 118 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_118 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 118) < 512 * (2 * m + 1) + 118 := by
  apply refinement_cleared (k := 9) (r := 118) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_118]; decide

end Collatz.Research.RefinementAtlas.Batch166
