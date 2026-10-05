import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 284. -/
namespace Collatz.Research.RefinementAtlas.Batch284
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 79). -/
theorem data_10_79 : oddCount 79 10 = 5 ∧
    acceleratedOrbit 10 79 = 19 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_79 : gap 10 79 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_79 : threshold 10 79 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_79 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 79) = 243 * (2 * m) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 79
  rw [data_10_79.1, data_10_79.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_79 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 79) = 243 * (2 * m + 1) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 79
  rw [data_10_79.1, data_10_79.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_79 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 79) < 1024 * (2 * m) + 79 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 79 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_79] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 79) < 1024 * (2 * m) + 79 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_79 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 79) < 1024 * (2 * m + 1) + 79 := by
  apply refinement_cleared (k := 10) (r := 79) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_79]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 80). -/
theorem data_10_80 : oddCount 80 10 = 2 ∧
    acceleratedOrbit 10 80 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_80 : gap 10 80 = 1015 ∧ 9 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_80 : threshold 10 80 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_80 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 80) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 80
  rw [data_10_80.1, data_10_80.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_80 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 80) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 80
  rw [data_10_80.1, data_10_80.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_80 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 80) < 1024 * (2 * m) + 80 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 80 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_80] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 80) < 1024 * (2 * m) + 80 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_80 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 80) < 1024 * (2 * m + 1) + 80 := by
  apply refinement_cleared (k := 10) (r := 80) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_80]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 81). -/
theorem data_10_81 : oddCount 81 10 = 5 ∧
    acceleratedOrbit 10 81 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_81 : gap 10 81 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_81 : threshold 10 81 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_81 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 81) = 243 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 81
  rw [data_10_81.1, data_10_81.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_81 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 81) = 243 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 81
  rw [data_10_81.1, data_10_81.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_81 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 81) < 1024 * (2 * m) + 81 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 81 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_81] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 81) < 1024 * (2 * m) + 81 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_81 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 81) < 1024 * (2 * m + 1) + 81 := by
  apply refinement_cleared (k := 10) (r := 81) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_81]; decide

end Collatz.Research.RefinementAtlas.Batch284
