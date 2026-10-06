import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 280. -/
namespace Collatz.Research.RefinementAtlas.Batch280
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 65). -/
theorem data_10_65 : oddCount 65 10 = 5 ∧
    acceleratedOrbit 10 65 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_65 : gap 10 65 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_65 : threshold 10 65 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_65 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 65) = 243 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 65
  rw [data_10_65.1, data_10_65.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_65 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 65) = 243 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 65
  rw [data_10_65.1, data_10_65.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_65 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 65) < 1024 * (2 * m) + 65 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 65 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_65] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 65) < 1024 * (2 * m) + 65 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_65 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 65) < 1024 * (2 * m + 1) + 65 := by
  apply refinement_cleared (k := 10) (r := 65) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_65]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 66). -/
theorem data_10_66 : oddCount 66 10 = 5 ∧
    acceleratedOrbit 10 66 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_66 : gap 10 66 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_66 : threshold 10 66 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_66 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 66) = 243 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 66
  rw [data_10_66.1, data_10_66.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_66 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 66) = 243 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 66
  rw [data_10_66.1, data_10_66.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_66 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 66) < 1024 * (2 * m) + 66 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 66 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_66] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 66) < 1024 * (2 * m) + 66 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_66 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 66) < 1024 * (2 * m + 1) + 66 := by
  apply refinement_cleared (k := 10) (r := 66) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_66]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 67). -/
theorem data_10_67 : oddCount 67 10 = 5 ∧
    acceleratedOrbit 10 67 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_67 : gap 10 67 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_67 : threshold 10 67 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_67 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 67) = 243 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 67
  rw [data_10_67.1, data_10_67.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_67 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 67) = 243 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 67
  rw [data_10_67.1, data_10_67.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_67 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 67) < 1024 * (2 * m) + 67 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 67 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_67] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 67) < 1024 * (2 * m) + 67 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_67 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 67) < 1024 * (2 * m + 1) + 67 := by
  apply refinement_cleared (k := 10) (r := 67) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_67]; decide

end Collatz.Research.RefinementAtlas.Batch280
