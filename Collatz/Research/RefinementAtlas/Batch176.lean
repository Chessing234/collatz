import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 176. -/
namespace Collatz.Research.RefinementAtlas.Batch176
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 156). -/
theorem data_9_156 : oddCount 156 9 = 5 ∧
    acceleratedOrbit 9 156 = 76 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_156 : gap 9 156 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_156 : threshold 9 156 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_156 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 156) = 243 * (2 * m) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 156
  rw [data_9_156.1, data_9_156.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_156 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 156) = 243 * (2 * m + 1) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 156
  rw [data_9_156.1, data_9_156.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_156 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 156) < 512 * (2 * m) + 156 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 156 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_156] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 156) < 512 * (2 * m) + 156 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_156 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 156) < 512 * (2 * m + 1) + 156 := by
  apply refinement_cleared (k := 9) (r := 156) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_156]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 157). -/
theorem data_9_157 : oddCount 157 9 = 5 ∧
    acceleratedOrbit 9 157 = 76 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_157 : gap 9 157 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_157 : threshold 9 157 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_157 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 157) = 243 * (2 * m) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 157
  rw [data_9_157.1, data_9_157.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_157 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 157) = 243 * (2 * m + 1) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 157
  rw [data_9_157.1, data_9_157.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_157 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 157) < 512 * (2 * m) + 157 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 157 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_157] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 157) < 512 * (2 * m) + 157 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_157 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 157) < 512 * (2 * m + 1) + 157 := by
  apply refinement_cleared (k := 9) (r := 157) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_157]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 158). -/
theorem data_9_158 : oddCount 158 9 = 5 ∧
    acceleratedOrbit 9 158 = 76 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_158 : gap 9 158 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_158 : threshold 9 158 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_158 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 158) = 243 * (2 * m) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 158
  rw [data_9_158.1, data_9_158.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_158 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 158) = 243 * (2 * m + 1) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 158
  rw [data_9_158.1, data_9_158.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_158 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 158) < 512 * (2 * m) + 158 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 158 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_158] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 158) < 512 * (2 * m) + 158 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_158 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 158) < 512 * (2 * m + 1) + 158 := by
  apply refinement_cleared (k := 9) (r := 158) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_158]; decide

end Collatz.Research.RefinementAtlas.Batch176
