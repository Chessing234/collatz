import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 162. -/
namespace Collatz.Research.RefinementAtlas.Batch162
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 97). -/
theorem data_9_97 : oddCount 97 9 = 5 ∧
    acceleratedOrbit 9 97 = 47 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_97 : gap 9 97 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_97 : threshold 9 97 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_97 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 97) = 243 * (2 * m) + 47 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 97
  rw [data_9_97.1, data_9_97.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_97 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 97) = 243 * (2 * m + 1) + 47 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 97
  rw [data_9_97.1, data_9_97.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_97 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 97) < 512 * (2 * m) + 97 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 97 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_97] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 97) < 512 * (2 * m) + 97 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_97 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 97) < 512 * (2 * m + 1) + 97 := by
  apply refinement_cleared (k := 9) (r := 97) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_97]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 98). -/
theorem data_9_98 : oddCount 98 9 = 4 ∧
    acceleratedOrbit 9 98 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_98 : gap 9 98 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_98 : threshold 9 98 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_98 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 98) = 81 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 98
  rw [data_9_98.1, data_9_98.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_98 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 98) = 81 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 98
  rw [data_9_98.1, data_9_98.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_98 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 98) < 512 * (2 * m) + 98 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 98 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_98] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 98) < 512 * (2 * m) + 98 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_98 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 98) < 512 * (2 * m + 1) + 98 := by
  apply refinement_cleared (k := 9) (r := 98) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_98]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 99). -/
theorem data_9_99 : oddCount 99 9 = 4 ∧
    acceleratedOrbit 9 99 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_99 : gap 9 99 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_99 : threshold 9 99 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_99 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 99) = 81 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 99
  rw [data_9_99.1, data_9_99.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_99 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 99) = 81 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 99
  rw [data_9_99.1, data_9_99.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_99 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 99) < 512 * (2 * m) + 99 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 99 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_99] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 99) < 512 * (2 * m) + 99 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_99 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 99) < 512 * (2 * m + 1) + 99 := by
  apply refinement_cleared (k := 9) (r := 99) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_99]; decide

end Collatz.Research.RefinementAtlas.Batch162
