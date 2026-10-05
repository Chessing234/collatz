import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 289. -/
namespace Collatz.Research.RefinementAtlas.Batch289
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 99). -/
theorem data_10_99 : oddCount 99 10 = 5 ∧
    acceleratedOrbit 10 99 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_99 : gap 10 99 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_99 : threshold 10 99 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_99 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 99) = 243 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 99
  rw [data_10_99.1, data_10_99.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_99 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 99) = 243 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 99
  rw [data_10_99.1, data_10_99.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_99 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 99) < 1024 * (2 * m) + 99 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 99 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_99] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 99) < 1024 * (2 * m) + 99 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_99 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 99) < 1024 * (2 * m + 1) + 99 := by
  apply refinement_cleared (k := 10) (r := 99) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_99]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 100). -/
theorem data_10_100 : oddCount 100 10 = 5 ∧
    acceleratedOrbit 10 100 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_100 : gap 10 100 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_100 : threshold 10 100 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_100 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 100) = 243 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 100
  rw [data_10_100.1, data_10_100.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_100 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 100) = 243 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 100
  rw [data_10_100.1, data_10_100.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_100 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 100) < 1024 * (2 * m) + 100 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 100 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_100] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 100) < 1024 * (2 * m) + 100 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_100 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 100) < 1024 * (2 * m + 1) + 100 := by
  apply refinement_cleared (k := 10) (r := 100) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_100]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 101). -/
theorem data_10_101 : oddCount 101 10 = 5 ∧
    acceleratedOrbit 10 101 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_101 : gap 10 101 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_101 : threshold 10 101 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_101 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 101) = 243 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 101
  rw [data_10_101.1, data_10_101.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_101 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 101) = 243 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 101
  rw [data_10_101.1, data_10_101.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_101 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 101) < 1024 * (2 * m) + 101 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 101 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_101] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 101) < 1024 * (2 * m) + 101 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_101 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 101) < 1024 * (2 * m + 1) + 101 := by
  apply refinement_cleared (k := 10) (r := 101) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_101]; decide

end Collatz.Research.RefinementAtlas.Batch289
