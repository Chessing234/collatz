import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 266. -/
namespace Collatz.Research.RefinementAtlas.Batch266
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 15). -/
theorem data_10_15 : oddCount 15 10 = 5 ∧
    acceleratedOrbit 10 15 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_15 : gap 10 15 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_15 : threshold 10 15 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_15 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 15) = 243 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 15
  rw [data_10_15.1, data_10_15.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_15 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 15) = 243 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 15
  rw [data_10_15.1, data_10_15.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_15 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 15) < 1024 * (2 * m) + 15 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 15 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_15] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 15) < 1024 * (2 * m) + 15 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_15 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 15) < 1024 * (2 * m + 1) + 15 := by
  apply refinement_cleared (k := 10) (r := 15) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_15]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 16). -/
theorem data_10_16 : oddCount 16 10 = 3 ∧
    acceleratedOrbit 10 16 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_16 : gap 10 16 = 997 ∧ 27 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_16 : threshold 10 16 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_16 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 16) = 27 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 16
  rw [data_10_16.1, data_10_16.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_16 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 16) = 27 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 16
  rw [data_10_16.1, data_10_16.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_16 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 16) < 1024 * (2 * m) + 16 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 16 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_16] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 16) < 1024 * (2 * m) + 16 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_16 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 16) < 1024 * (2 * m + 1) + 16 := by
  apply refinement_cleared (k := 10) (r := 16) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_16]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 17). -/
theorem data_10_17 : oddCount 17 10 = 4 ∧
    acceleratedOrbit 10 17 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_17 : gap 10 17 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_17 : threshold 10 17 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_17 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 17) = 81 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 17
  rw [data_10_17.1, data_10_17.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_17 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 17) = 81 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 17
  rw [data_10_17.1, data_10_17.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_17 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 17) < 1024 * (2 * m) + 17 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 17 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_17] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 17) < 1024 * (2 * m) + 17 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_17 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 17) < 1024 * (2 * m + 1) + 17 := by
  apply refinement_cleared (k := 10) (r := 17) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_17]; decide

end Collatz.Research.RefinementAtlas.Batch266
