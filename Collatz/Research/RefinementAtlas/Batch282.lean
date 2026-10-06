import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 282. -/
namespace Collatz.Research.RefinementAtlas.Batch282
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 72). -/
theorem data_10_72 : oddCount 72 10 = 5 ∧
    acceleratedOrbit 10 72 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_72 : gap 10 72 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_72 : threshold 10 72 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_72 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 72) = 243 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 72
  rw [data_10_72.1, data_10_72.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_72 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 72) = 243 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 72
  rw [data_10_72.1, data_10_72.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_72 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 72) < 1024 * (2 * m) + 72 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 72 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_72] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 72) < 1024 * (2 * m) + 72 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_72 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 72) < 1024 * (2 * m + 1) + 72 := by
  apply refinement_cleared (k := 10) (r := 72) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_72]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 74). -/
theorem data_10_74 : oddCount 74 10 = 5 ∧
    acceleratedOrbit 10 74 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_74 : gap 10 74 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_74 : threshold 10 74 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_74 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 74) = 243 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 74
  rw [data_10_74.1, data_10_74.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_74 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 74) = 243 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 74
  rw [data_10_74.1, data_10_74.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_74 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 74) < 1024 * (2 * m) + 74 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 74 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_74] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 74) < 1024 * (2 * m) + 74 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_74 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 74) < 1024 * (2 * m + 1) + 74 := by
  apply refinement_cleared (k := 10) (r := 74) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_74]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 75). -/
theorem data_10_75 : oddCount 75 10 = 3 ∧
    acceleratedOrbit 10 75 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_75 : gap 10 75 = 997 ∧ 27 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_75 : threshold 10 75 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_75 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 75) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 75
  rw [data_10_75.1, data_10_75.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_75 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 75) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 75
  rw [data_10_75.1, data_10_75.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_75 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 75) < 1024 * (2 * m) + 75 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 75 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_75] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 75) < 1024 * (2 * m) + 75 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_75 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 75) < 1024 * (2 * m + 1) + 75 := by
  apply refinement_cleared (k := 10) (r := 75) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_75]; decide

end Collatz.Research.RefinementAtlas.Batch282
