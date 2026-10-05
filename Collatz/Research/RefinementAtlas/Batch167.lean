import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 167. -/
namespace Collatz.Research.RefinementAtlas.Batch167
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 119). -/
theorem data_9_119 : oddCount 119 9 = 4 ∧
    acceleratedOrbit 9 119 = 19 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_119 : gap 9 119 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_119 : threshold 9 119 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_119 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 119) = 81 * (2 * m) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 119
  rw [data_9_119.1, data_9_119.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_119 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 119) = 81 * (2 * m + 1) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 119
  rw [data_9_119.1, data_9_119.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_119 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 119) < 512 * (2 * m) + 119 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 119 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_119] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 119) < 512 * (2 * m) + 119 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_119 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 119) < 512 * (2 * m + 1) + 119 := by
  apply refinement_cleared (k := 9) (r := 119) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_119]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 120). -/
theorem data_9_120 : oddCount 120 9 = 4 ∧
    acceleratedOrbit 9 120 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_120 : gap 9 120 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_120 : threshold 9 120 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_120 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 120) = 81 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 120
  rw [data_9_120.1, data_9_120.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_120 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 120) = 81 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 120
  rw [data_9_120.1, data_9_120.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_120 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 120) < 512 * (2 * m) + 120 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 120 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_120] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 120) < 512 * (2 * m) + 120 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_120 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 120) < 512 * (2 * m + 1) + 120 := by
  apply refinement_cleared (k := 9) (r := 120) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_120]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 122). -/
theorem data_9_122 : oddCount 122 9 = 4 ∧
    acceleratedOrbit 9 122 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_122 : gap 9 122 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_122 : threshold 9 122 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_122 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 122) = 81 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 122
  rw [data_9_122.1, data_9_122.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_122 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 122) = 81 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 122
  rw [data_9_122.1, data_9_122.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_122 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 122) < 512 * (2 * m) + 122 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 122 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_122] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 122) < 512 * (2 * m) + 122 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_122 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 122) < 512 * (2 * m + 1) + 122 := by
  apply refinement_cleared (k := 9) (r := 122) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_122]; decide

end Collatz.Research.RefinementAtlas.Batch167
