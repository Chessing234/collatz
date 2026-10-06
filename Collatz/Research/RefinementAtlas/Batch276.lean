import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 276. -/
namespace Collatz.Research.RefinementAtlas.Batch276
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 49). -/
theorem data_10_49 : oddCount 49 10 = 5 ∧
    acceleratedOrbit 10 49 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_49 : gap 10 49 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_49 : threshold 10 49 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_49 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 49) = 243 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 49
  rw [data_10_49.1, data_10_49.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_49 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 49) = 243 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 49
  rw [data_10_49.1, data_10_49.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_49 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 49) < 1024 * (2 * m) + 49 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 49 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_49] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 49) < 1024 * (2 * m) + 49 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_49 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 49) < 1024 * (2 * m + 1) + 49 := by
  apply refinement_cleared (k := 10) (r := 49) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_49]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 50). -/
theorem data_10_50 : oddCount 50 10 = 5 ∧
    acceleratedOrbit 10 50 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_50 : gap 10 50 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_50 : threshold 10 50 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_50 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 50) = 243 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 50
  rw [data_10_50.1, data_10_50.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_50 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 50) = 243 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 50
  rw [data_10_50.1, data_10_50.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_50 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 50) < 1024 * (2 * m) + 50 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 50 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_50] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 50) < 1024 * (2 * m) + 50 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_50 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 50) < 1024 * (2 * m + 1) + 50 := by
  apply refinement_cleared (k := 10) (r := 50) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_50]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 51). -/
theorem data_10_51 : oddCount 51 10 = 5 ∧
    acceleratedOrbit 10 51 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_51 : gap 10 51 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_51 : threshold 10 51 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_51 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 51) = 243 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 51
  rw [data_10_51.1, data_10_51.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_51 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 51) = 243 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 51
  rw [data_10_51.1, data_10_51.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_51 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 51) < 1024 * (2 * m) + 51 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 51 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_51] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 51) < 1024 * (2 * m) + 51 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_51 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 51) < 1024 * (2 * m + 1) + 51 := by
  apply refinement_cleared (k := 10) (r := 51) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_51]; decide

end Collatz.Research.RefinementAtlas.Batch276
