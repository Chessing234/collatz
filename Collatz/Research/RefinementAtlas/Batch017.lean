import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 017. -/
namespace Collatz.Research.RefinementAtlas.Batch017
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (5, 21). -/
theorem data_5_21 : oddCount 21 5 = 1 ∧
    acceleratedOrbit 5 21 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_21 : gap 5 21 = 29 ∧ 3 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_21 : threshold 5 21 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_21 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 21) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 21
  rw [data_5_21.1, data_5_21.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_21 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 21) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 21
  rw [data_5_21.1, data_5_21.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_21 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 21) < 32 * (2 * m) + 21 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 21 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_21] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 21) < 32 * (2 * m) + 21 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_21 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 21) < 32 * (2 * m + 1) + 21 := by
  apply refinement_cleared (k := 5) (r := 21) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_21]; decide

/-- Kernel-evaluated parity count and endpoint for (5, 22). -/
theorem data_5_22 : oddCount 22 5 = 3 ∧
    acceleratedOrbit 5 22 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_22 : gap 5 22 = 5 ∧ 27 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_22 : threshold 5 22 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_22 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 22) = 27 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 22
  rw [data_5_22.1, data_5_22.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_22 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 22) = 27 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 22
  rw [data_5_22.1, data_5_22.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_22 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 22) < 32 * (2 * m) + 22 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 22 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_22] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 22) < 32 * (2 * m) + 22 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_22 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 22) < 32 * (2 * m + 1) + 22 := by
  apply refinement_cleared (k := 5) (r := 22) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_22]; decide

/-- Kernel-evaluated parity count and endpoint for (5, 23). -/
theorem data_5_23 : oddCount 23 5 = 3 ∧
    acceleratedOrbit 5 23 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_23 : gap 5 23 = 5 ∧ 27 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_23 : threshold 5 23 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_23 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 23) = 27 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 23
  rw [data_5_23.1, data_5_23.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_23 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 23) = 27 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 23
  rw [data_5_23.1, data_5_23.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_23 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 23) < 32 * (2 * m) + 23 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 23 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_23] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 23) < 32 * (2 * m) + 23 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_23 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 23) < 32 * (2 * m + 1) + 23 := by
  apply refinement_cleared (k := 5) (r := 23) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_23]; decide

end Collatz.Research.RefinementAtlas.Batch017
