import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 163. -/
namespace Collatz.Research.RefinementAtlas.Batch163
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 100). -/
theorem data_9_100 : oddCount 100 9 = 4 ∧
    acceleratedOrbit 9 100 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_100 : gap 9 100 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_100 : threshold 9 100 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_100 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 100) = 81 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 100
  rw [data_9_100.1, data_9_100.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_100 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 100) = 81 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 100
  rw [data_9_100.1, data_9_100.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_100 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 100) < 512 * (2 * m) + 100 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 100 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_100] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 100) < 512 * (2 * m) + 100 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_100 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 100) < 512 * (2 * m + 1) + 100 := by
  apply refinement_cleared (k := 9) (r := 100) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_100]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 101). -/
theorem data_9_101 : oddCount 101 9 = 4 ∧
    acceleratedOrbit 9 101 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_101 : gap 9 101 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_101 : threshold 9 101 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_101 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 101) = 81 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 101
  rw [data_9_101.1, data_9_101.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_101 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 101) = 81 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 101
  rw [data_9_101.1, data_9_101.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_101 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 101) < 512 * (2 * m) + 101 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 101 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_101] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 101) < 512 * (2 * m) + 101 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_101 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 101) < 512 * (2 * m + 1) + 101 := by
  apply refinement_cleared (k := 9) (r := 101) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_101]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 102). -/
theorem data_9_102 : oddCount 102 9 = 4 ∧
    acceleratedOrbit 9 102 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_102 : gap 9 102 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_102 : threshold 9 102 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_102 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 102) = 81 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 102
  rw [data_9_102.1, data_9_102.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_102 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 102) = 81 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 102
  rw [data_9_102.1, data_9_102.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_102 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 102) < 512 * (2 * m) + 102 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 102 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_102] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 102) < 512 * (2 * m) + 102 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_102 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 102) < 512 * (2 * m + 1) + 102 := by
  apply refinement_cleared (k := 9) (r := 102) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_102]; decide

end Collatz.Research.RefinementAtlas.Batch163
