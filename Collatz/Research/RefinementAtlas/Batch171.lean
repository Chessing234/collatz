import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 171. -/
namespace Collatz.Research.RefinementAtlas.Batch171
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 138). -/
theorem data_9_138 : oddCount 138 9 = 3 ∧
    acceleratedOrbit 9 138 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_138 : gap 9 138 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_138 : threshold 9 138 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_138 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 138) = 27 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 138
  rw [data_9_138.1, data_9_138.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_138 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 138) = 27 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 138
  rw [data_9_138.1, data_9_138.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_138 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 138) < 512 * (2 * m) + 138 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 138 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_138] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 138) < 512 * (2 * m) + 138 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_138 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 138) < 512 * (2 * m + 1) + 138 := by
  apply refinement_cleared (k := 9) (r := 138) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_138]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 139). -/
theorem data_9_139 : oddCount 139 9 = 5 ∧
    acceleratedOrbit 9 139 = 67 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_139 : gap 9 139 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_139 : threshold 9 139 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_139 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 139) = 243 * (2 * m) + 67 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 139
  rw [data_9_139.1, data_9_139.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_139 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 139) = 243 * (2 * m + 1) + 67 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 139
  rw [data_9_139.1, data_9_139.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_139 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 139) < 512 * (2 * m) + 139 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 139 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_139] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 139) < 512 * (2 * m) + 139 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_139 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 139) < 512 * (2 * m + 1) + 139 := by
  apply refinement_cleared (k := 9) (r := 139) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_139]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 140). -/
theorem data_9_140 : oddCount 140 9 = 3 ∧
    acceleratedOrbit 9 140 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_140 : gap 9 140 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_140 : threshold 9 140 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_140 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 140) = 27 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 140
  rw [data_9_140.1, data_9_140.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_140 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 140) = 27 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 140
  rw [data_9_140.1, data_9_140.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_140 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 140) < 512 * (2 * m) + 140 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 140 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_140] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 140) < 512 * (2 * m) + 140 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_140 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 140) < 512 * (2 * m + 1) + 140 := by
  apply refinement_cleared (k := 9) (r := 140) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_140]; decide

end Collatz.Research.RefinementAtlas.Batch171
