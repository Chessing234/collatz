import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 178. -/
namespace Collatz.Research.RefinementAtlas.Batch178
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 168). -/
theorem data_9_168 : oddCount 168 9 = 1 ∧
    acceleratedOrbit 9 168 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_168 : gap 9 168 = 509 ∧ 3 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_168 : threshold 9 168 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_168 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 168) = 3 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 168
  rw [data_9_168.1, data_9_168.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_168 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 168) = 3 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 168
  rw [data_9_168.1, data_9_168.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_168 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 168) < 512 * (2 * m) + 168 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 168 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_168] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 168) < 512 * (2 * m) + 168 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_168 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 168) < 512 * (2 * m + 1) + 168 := by
  apply refinement_cleared (k := 9) (r := 168) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_168]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 170). -/
theorem data_9_170 : oddCount 170 9 = 1 ∧
    acceleratedOrbit 9 170 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_170 : gap 9 170 = 509 ∧ 3 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_170 : threshold 9 170 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_170 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 170) = 3 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 170
  rw [data_9_170.1, data_9_170.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_170 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 170) = 3 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 170
  rw [data_9_170.1, data_9_170.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_170 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 170) < 512 * (2 * m) + 170 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 170 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_170] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 170) < 512 * (2 * m) + 170 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_170 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 170) < 512 * (2 * m + 1) + 170 := by
  apply refinement_cleared (k := 9) (r := 170) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_170]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 171). -/
theorem data_9_171 : oddCount 171 9 = 5 ∧
    acceleratedOrbit 9 171 = 82 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_171 : gap 9 171 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_171 : threshold 9 171 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_171 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 171) = 243 * (2 * m) + 82 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 171
  rw [data_9_171.1, data_9_171.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_171 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 171) = 243 * (2 * m + 1) + 82 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 171
  rw [data_9_171.1, data_9_171.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_171 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 171) < 512 * (2 * m) + 171 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 171 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_171] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 171) < 512 * (2 * m) + 171 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_171 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 171) < 512 * (2 * m + 1) + 171 := by
  apply refinement_cleared (k := 9) (r := 171) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_171]; decide

end Collatz.Research.RefinementAtlas.Batch178
