import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 136. -/
namespace Collatz.Research.RefinementAtlas.Batch136
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 4). -/
theorem data_9_4 : oddCount 4 9 = 4 ∧
    acceleratedOrbit 9 4 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_4 : gap 9 4 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_4 : threshold 9 4 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_4 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 4) = 81 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 4
  rw [data_9_4.1, data_9_4.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_4 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 4) = 81 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 4
  rw [data_9_4.1, data_9_4.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_4 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 4) < 512 * (2 * m) + 4 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 4 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_4] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 4) < 512 * (2 * m) + 4 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_4 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 4) < 512 * (2 * m + 1) + 4 := by
  apply refinement_cleared (k := 9) (r := 4) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_4]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 5). -/
theorem data_9_5 : oddCount 5 9 = 4 ∧
    acceleratedOrbit 9 5 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_5 : gap 9 5 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_5 : threshold 9 5 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_5 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 5) = 81 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 5
  rw [data_9_5.1, data_9_5.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_5 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 5) = 81 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 5
  rw [data_9_5.1, data_9_5.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_5 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 5) < 512 * (2 * m) + 5 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 5 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_5] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 5) < 512 * (2 * m) + 5 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_5 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 5) < 512 * (2 * m + 1) + 5 := by
  apply refinement_cleared (k := 9) (r := 5) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_5]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 6). -/
theorem data_9_6 : oddCount 6 9 = 4 ∧
    acceleratedOrbit 9 6 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_6 : gap 9 6 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_6 : threshold 9 6 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_6 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 6) = 81 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 6
  rw [data_9_6.1, data_9_6.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_6 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 6) = 81 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 6
  rw [data_9_6.1, data_9_6.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_6 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 6) < 512 * (2 * m) + 6 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 6 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_6] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 6) < 512 * (2 * m) + 6 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_6 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 6) < 512 * (2 * m + 1) + 6 := by
  apply refinement_cleared (k := 9) (r := 6) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_6]; decide

end Collatz.Research.RefinementAtlas.Batch136
