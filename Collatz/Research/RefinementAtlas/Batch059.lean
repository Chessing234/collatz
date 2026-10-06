import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 059. -/
namespace Collatz.Research.RefinementAtlas.Batch059
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 100). -/
theorem data_7_100 : oddCount 100 7 = 3 ∧
    acceleratedOrbit 7 100 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_100 : gap 7 100 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_100 : threshold 7 100 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_100 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 100) = 27 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 100
  rw [data_7_100.1, data_7_100.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_100 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 100) = 27 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 100
  rw [data_7_100.1, data_7_100.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_100 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 100) < 128 * (2 * m) + 100 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 100 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_100] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 100) < 128 * (2 * m) + 100 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_100 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 100) < 128 * (2 * m + 1) + 100 := by
  apply refinement_cleared (k := 7) (r := 100) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_100]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 101). -/
theorem data_7_101 : oddCount 101 7 = 3 ∧
    acceleratedOrbit 7 101 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_101 : gap 7 101 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_101 : threshold 7 101 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_101 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 101) = 27 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 101
  rw [data_7_101.1, data_7_101.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_101 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 101) = 27 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 101
  rw [data_7_101.1, data_7_101.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_101 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 101) < 128 * (2 * m) + 101 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 101 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_101] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 101) < 128 * (2 * m) + 101 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_101 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 101) < 128 * (2 * m + 1) + 101 := by
  apply refinement_cleared (k := 7) (r := 101) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_101]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 102). -/
theorem data_7_102 : oddCount 102 7 = 3 ∧
    acceleratedOrbit 7 102 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_102 : gap 7 102 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_102 : threshold 7 102 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_102 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 102) = 27 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 102
  rw [data_7_102.1, data_7_102.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_102 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 102) = 27 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 102
  rw [data_7_102.1, data_7_102.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_102 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 102) < 128 * (2 * m) + 102 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 102 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_102] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 102) < 128 * (2 * m) + 102 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_102 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 102) < 128 * (2 * m + 1) + 102 := by
  apply refinement_cleared (k := 7) (r := 102) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_102]; decide

end Collatz.Research.RefinementAtlas.Batch059
