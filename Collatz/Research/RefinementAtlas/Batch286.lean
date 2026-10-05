import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 286. -/
namespace Collatz.Research.RefinementAtlas.Batch286
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 87). -/
theorem data_10_87 : oddCount 87 10 = 4 ∧
    acceleratedOrbit 10 87 = 7 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_87 : gap 10 87 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_87 : threshold 10 87 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_87 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 87) = 81 * (2 * m) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 87
  rw [data_10_87.1, data_10_87.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_87 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 87) = 81 * (2 * m + 1) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 87
  rw [data_10_87.1, data_10_87.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_87 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 87) < 1024 * (2 * m) + 87 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 87 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_87] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 87) < 1024 * (2 * m) + 87 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_87 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 87) < 1024 * (2 * m + 1) + 87 := by
  apply refinement_cleared (k := 10) (r := 87) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_87]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 88). -/
theorem data_10_88 : oddCount 88 10 = 4 ∧
    acceleratedOrbit 10 88 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_88 : gap 10 88 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_88 : threshold 10 88 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_88 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 88) = 81 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 88
  rw [data_10_88.1, data_10_88.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_88 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 88) = 81 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 88
  rw [data_10_88.1, data_10_88.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_88 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 88) < 1024 * (2 * m) + 88 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 88 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_88] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 88) < 1024 * (2 * m) + 88 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_88 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 88) < 1024 * (2 * m + 1) + 88 := by
  apply refinement_cleared (k := 10) (r := 88) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_88]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 89). -/
theorem data_10_89 : oddCount 89 10 = 5 ∧
    acceleratedOrbit 10 89 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_89 : gap 10 89 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_89 : threshold 10 89 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_89 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 89) = 243 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 89
  rw [data_10_89.1, data_10_89.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_89 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 89) = 243 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 89
  rw [data_10_89.1, data_10_89.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_89 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 89) < 1024 * (2 * m) + 89 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 89 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_89] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 89) < 1024 * (2 * m) + 89 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_89 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 89) < 1024 * (2 * m + 1) + 89 := by
  apply refinement_cleared (k := 10) (r := 89) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_89]; decide

end Collatz.Research.RefinementAtlas.Batch286
