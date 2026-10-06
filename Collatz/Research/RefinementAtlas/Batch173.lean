import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 173. -/
namespace Collatz.Research.RefinementAtlas.Batch173
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 146). -/
theorem data_9_146 : oddCount 146 9 = 5 ∧
    acceleratedOrbit 9 146 = 71 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_146 : gap 9 146 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_146 : threshold 9 146 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_146 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 146) = 243 * (2 * m) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 146
  rw [data_9_146.1, data_9_146.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_146 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 146) = 243 * (2 * m + 1) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 146
  rw [data_9_146.1, data_9_146.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_146 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 146) < 512 * (2 * m) + 146 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 146 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_146] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 146) < 512 * (2 * m) + 146 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_146 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 146) < 512 * (2 * m + 1) + 146 := by
  apply refinement_cleared (k := 9) (r := 146) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_146]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 147). -/
theorem data_9_147 : oddCount 147 9 = 5 ∧
    acceleratedOrbit 9 147 = 71 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_147 : gap 9 147 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_147 : threshold 9 147 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_147 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 147) = 243 * (2 * m) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 147
  rw [data_9_147.1, data_9_147.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_147 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 147) = 243 * (2 * m + 1) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 147
  rw [data_9_147.1, data_9_147.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_147 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 147) < 512 * (2 * m) + 147 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 147 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_147] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 147) < 512 * (2 * m) + 147 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_147 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 147) < 512 * (2 * m + 1) + 147 := by
  apply refinement_cleared (k := 9) (r := 147) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_147]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 148). -/
theorem data_9_148 : oddCount 148 9 = 4 ∧
    acceleratedOrbit 9 148 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_148 : gap 9 148 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_148 : threshold 9 148 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_148 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 148) = 81 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 148
  rw [data_9_148.1, data_9_148.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_148 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 148) = 81 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 148
  rw [data_9_148.1, data_9_148.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_148 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 148) < 512 * (2 * m) + 148 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 148 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_148] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 148) < 512 * (2 * m) + 148 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_148 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 148) < 512 * (2 * m + 1) + 148 := by
  apply refinement_cleared (k := 9) (r := 148) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_148]; decide

end Collatz.Research.RefinementAtlas.Batch173
