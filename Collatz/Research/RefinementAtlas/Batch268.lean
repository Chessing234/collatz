import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 268. -/
namespace Collatz.Research.RefinementAtlas.Batch268
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 21). -/
theorem data_10_21 : oddCount 21 10 = 3 ∧
    acceleratedOrbit 10 21 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_21 : gap 10 21 = 997 ∧ 27 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_21 : threshold 10 21 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_21 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 21) = 27 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 21
  rw [data_10_21.1, data_10_21.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_21 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 21) = 27 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 21
  rw [data_10_21.1, data_10_21.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_21 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 21) < 1024 * (2 * m) + 21 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 21 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_21] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 21) < 1024 * (2 * m) + 21 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_21 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 21) < 1024 * (2 * m + 1) + 21 := by
  apply refinement_cleared (k := 10) (r := 21) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_21]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 22). -/
theorem data_10_22 : oddCount 22 10 = 4 ∧
    acceleratedOrbit 10 22 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_22 : gap 10 22 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_22 : threshold 10 22 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_22 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 22) = 81 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 22
  rw [data_10_22.1, data_10_22.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_22 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 22) = 81 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 22
  rw [data_10_22.1, data_10_22.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_22 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 22) < 1024 * (2 * m) + 22 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 22 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_22] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 22) < 1024 * (2 * m) + 22 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_22 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 22) < 1024 * (2 * m + 1) + 22 := by
  apply refinement_cleared (k := 10) (r := 22) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_22]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 23). -/
theorem data_10_23 : oddCount 23 10 = 4 ∧
    acceleratedOrbit 10 23 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_23 : gap 10 23 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_23 : threshold 10 23 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_23 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 23) = 81 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 23
  rw [data_10_23.1, data_10_23.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_23 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 23) = 81 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 23
  rw [data_10_23.1, data_10_23.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_23 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 23) < 1024 * (2 * m) + 23 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 23 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_23] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 23) < 1024 * (2 * m) + 23 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_23 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 23) < 1024 * (2 * m + 1) + 23 := by
  apply refinement_cleared (k := 10) (r := 23) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_23]; decide

end Collatz.Research.RefinementAtlas.Batch268
