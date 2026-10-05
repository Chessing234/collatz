import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 170. -/
namespace Collatz.Research.RefinementAtlas.Batch170
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 134). -/
theorem data_9_134 : oddCount 134 9 = 4 ∧
    acceleratedOrbit 9 134 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_134 : gap 9 134 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_134 : threshold 9 134 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_134 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 134) = 81 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 134
  rw [data_9_134.1, data_9_134.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_134 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 134) = 81 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 134
  rw [data_9_134.1, data_9_134.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_134 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 134) < 512 * (2 * m) + 134 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 134 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_134] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 134) < 512 * (2 * m) + 134 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_134 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 134) < 512 * (2 * m + 1) + 134 := by
  apply refinement_cleared (k := 9) (r := 134) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_134]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 135). -/
theorem data_9_135 : oddCount 135 9 = 5 ∧
    acceleratedOrbit 9 135 = 65 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_135 : gap 9 135 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_135 : threshold 9 135 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_135 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 135) = 243 * (2 * m) + 65 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 135
  rw [data_9_135.1, data_9_135.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_135 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 135) = 243 * (2 * m + 1) + 65 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 135
  rw [data_9_135.1, data_9_135.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_135 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 135) < 512 * (2 * m) + 135 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 135 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_135] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 135) < 512 * (2 * m) + 135 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_135 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 135) < 512 * (2 * m + 1) + 135 := by
  apply refinement_cleared (k := 9) (r := 135) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_135]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 136). -/
theorem data_9_136 : oddCount 136 9 = 3 ∧
    acceleratedOrbit 9 136 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_136 : gap 9 136 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_136 : threshold 9 136 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_136 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 136) = 27 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 136
  rw [data_9_136.1, data_9_136.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_136 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 136) = 27 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 136
  rw [data_9_136.1, data_9_136.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_136 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 136) < 512 * (2 * m) + 136 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 136 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_136] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 136) < 512 * (2 * m) + 136 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_136 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 136) < 512 * (2 * m + 1) + 136 := by
  apply refinement_cleared (k := 9) (r := 136) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_136]; decide

end Collatz.Research.RefinementAtlas.Batch170
