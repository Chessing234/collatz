import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 143. -/
namespace Collatz.Research.RefinementAtlas.Batch143
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 25). -/
theorem data_9_25 : oddCount 25 9 = 5 ∧
    acceleratedOrbit 9 25 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_25 : gap 9 25 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_25 : threshold 9 25 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_25 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 25) = 243 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 25
  rw [data_9_25.1, data_9_25.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_25 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 25) = 243 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 25
  rw [data_9_25.1, data_9_25.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_25 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 25) < 512 * (2 * m) + 25 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 25 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_25] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 25) < 512 * (2 * m) + 25 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_25 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 25) < 512 * (2 * m + 1) + 25 := by
  apply refinement_cleared (k := 9) (r := 25) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_25]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 26). -/
theorem data_9_26 : oddCount 26 9 = 3 ∧
    acceleratedOrbit 9 26 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_26 : gap 9 26 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_26 : threshold 9 26 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_26 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 26) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 26
  rw [data_9_26.1, data_9_26.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_26 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 26) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 26
  rw [data_9_26.1, data_9_26.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_26 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 26) < 512 * (2 * m) + 26 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 26 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_26] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 26) < 512 * (2 * m) + 26 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_26 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 26) < 512 * (2 * m + 1) + 26 := by
  apply refinement_cleared (k := 9) (r := 26) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_26]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 28). -/
theorem data_9_28 : oddCount 28 9 = 4 ∧
    acceleratedOrbit 9 28 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_28 : gap 9 28 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_28 : threshold 9 28 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_28 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 28) = 81 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 28
  rw [data_9_28.1, data_9_28.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_28 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 28) = 81 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 28
  rw [data_9_28.1, data_9_28.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_28 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 28) < 512 * (2 * m) + 28 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 28 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_28] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 28) < 512 * (2 * m) + 28 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_28 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 28) < 512 * (2 * m + 1) + 28 := by
  apply refinement_cleared (k := 9) (r := 28) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_28]; decide

end Collatz.Research.RefinementAtlas.Batch143
