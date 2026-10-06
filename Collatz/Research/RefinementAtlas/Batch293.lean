import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 293. -/
namespace Collatz.Research.RefinementAtlas.Batch293
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 117). -/
theorem data_10_117 : oddCount 117 10 = 4 ∧
    acceleratedOrbit 10 117 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_117 : gap 10 117 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_117 : threshold 10 117 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_117 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 117) = 81 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 117
  rw [data_10_117.1, data_10_117.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_117 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 117) = 81 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 117
  rw [data_10_117.1, data_10_117.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_117 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 117) < 1024 * (2 * m) + 117 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 117 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_117] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 117) < 1024 * (2 * m) + 117 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_117 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 117) < 1024 * (2 * m + 1) + 117 := by
  apply refinement_cleared (k := 10) (r := 117) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_117]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 118). -/
theorem data_10_118 : oddCount 118 10 = 5 ∧
    acceleratedOrbit 10 118 = 29 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_118 : gap 10 118 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_118 : threshold 10 118 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_118 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 118) = 243 * (2 * m) + 29 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 118
  rw [data_10_118.1, data_10_118.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_118 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 118) = 243 * (2 * m + 1) + 29 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 118
  rw [data_10_118.1, data_10_118.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_118 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 118) < 1024 * (2 * m) + 118 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 118 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_118] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 118) < 1024 * (2 * m) + 118 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_118 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 118) < 1024 * (2 * m + 1) + 118 := by
  apply refinement_cleared (k := 10) (r := 118) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_118]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 119). -/
theorem data_10_119 : oddCount 119 10 = 5 ∧
    acceleratedOrbit 10 119 = 29 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_119 : gap 10 119 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_119 : threshold 10 119 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_119 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 119) = 243 * (2 * m) + 29 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 119
  rw [data_10_119.1, data_10_119.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_119 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 119) = 243 * (2 * m + 1) + 29 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 119
  rw [data_10_119.1, data_10_119.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_119 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 119) < 1024 * (2 * m) + 119 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 119 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_119] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 119) < 1024 * (2 * m) + 119 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_119 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 119) < 1024 * (2 * m + 1) + 119 := by
  apply refinement_cleared (k := 10) (r := 119) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_119]; decide

end Collatz.Research.RefinementAtlas.Batch293
