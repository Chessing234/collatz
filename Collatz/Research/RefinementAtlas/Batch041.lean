import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 041. -/
namespace Collatz.Research.RefinementAtlas.Batch041
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 29). -/
theorem data_7_29 : oddCount 29 7 = 4 ∧
    acceleratedOrbit 7 29 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_29 : gap 7 29 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_29 : threshold 7 29 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_29 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 29) = 81 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 29
  rw [data_7_29.1, data_7_29.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_29 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 29) = 81 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 29
  rw [data_7_29.1, data_7_29.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_29 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 29) < 128 * (2 * m) + 29 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 29 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_29] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 29) < 128 * (2 * m) + 29 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_29 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 29) < 128 * (2 * m + 1) + 29 := by
  apply refinement_cleared (k := 7) (r := 29) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_29]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 30). -/
theorem data_7_30 : oddCount 30 7 = 4 ∧
    acceleratedOrbit 7 30 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_30 : gap 7 30 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_30 : threshold 7 30 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_30 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 30) = 81 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 30
  rw [data_7_30.1, data_7_30.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_30 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 30) = 81 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 30
  rw [data_7_30.1, data_7_30.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_30 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 30) < 128 * (2 * m) + 30 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 30 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_30] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 30) < 128 * (2 * m) + 30 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_30 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 30) < 128 * (2 * m + 1) + 30 := by
  apply refinement_cleared (k := 7) (r := 30) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_30]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 32). -/
theorem data_7_32 : oddCount 32 7 = 1 ∧
    acceleratedOrbit 7 32 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_32 : gap 7 32 = 125 ∧ 3 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_32 : threshold 7 32 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_32 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 32) = 3 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 32
  rw [data_7_32.1, data_7_32.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_32 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 32) = 3 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 32
  rw [data_7_32.1, data_7_32.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_32 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 32) < 128 * (2 * m) + 32 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 32 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_32] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 32) < 128 * (2 * m) + 32 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_32 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 32) < 128 * (2 * m + 1) + 32 := by
  apply refinement_cleared (k := 7) (r := 32) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_32]; decide

end Collatz.Research.RefinementAtlas.Batch041
