import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 015. -/
namespace Collatz.Research.RefinementAtlas.Batch015
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (5, 14). -/
theorem data_5_14 : oddCount 14 5 = 3 ∧
    acceleratedOrbit 5 14 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_14 : gap 5 14 = 5 ∧ 27 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_14 : threshold 5 14 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_14 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 14) = 27 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 14
  rw [data_5_14.1, data_5_14.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_14 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 14) = 27 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 14
  rw [data_5_14.1, data_5_14.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_14 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 14) < 32 * (2 * m) + 14 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 14 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_14] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 14) < 32 * (2 * m) + 14 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_14 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 14) < 32 * (2 * m + 1) + 14 := by
  apply refinement_cleared (k := 5) (r := 14) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_14]; decide

/-- Kernel-evaluated parity count and endpoint for (5, 16). -/
theorem data_5_16 : oddCount 16 5 = 1 ∧
    acceleratedOrbit 5 16 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_16 : gap 5 16 = 29 ∧ 3 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_16 : threshold 5 16 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_16 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 16) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 16
  rw [data_5_16.1, data_5_16.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_16 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 16) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 16
  rw [data_5_16.1, data_5_16.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_16 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 16) < 32 * (2 * m) + 16 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 16 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_16] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 16) < 32 * (2 * m) + 16 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_16 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 16) < 32 * (2 * m + 1) + 16 := by
  apply refinement_cleared (k := 5) (r := 16) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_16]; decide

/-- Kernel-evaluated parity count and endpoint for (5, 17). -/
theorem data_5_17 : oddCount 17 5 = 2 ∧
    acceleratedOrbit 5 17 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_17 : gap 5 17 = 23 ∧ 9 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_17 : threshold 5 17 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_17 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 17) = 9 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 17
  rw [data_5_17.1, data_5_17.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_17 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 17) = 9 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 17
  rw [data_5_17.1, data_5_17.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_17 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 17) < 32 * (2 * m) + 17 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 17 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_17] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 17) < 32 * (2 * m) + 17 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_17 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 17) < 32 * (2 * m + 1) + 17 := by
  apply refinement_cleared (k := 5) (r := 17) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_17]; decide

end Collatz.Research.RefinementAtlas.Batch015
