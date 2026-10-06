import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 157. -/
namespace Collatz.Research.RefinementAtlas.Batch157
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 77). -/
theorem data_9_77 : oddCount 77 9 = 4 ∧
    acceleratedOrbit 9 77 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_77 : gap 9 77 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_77 : threshold 9 77 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_77 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 77) = 81 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 77
  rw [data_9_77.1, data_9_77.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_77 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 77) = 81 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 77
  rw [data_9_77.1, data_9_77.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_77 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 77) < 512 * (2 * m) + 77 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 77 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_77] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 77) < 512 * (2 * m) + 77 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_77 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 77) < 512 * (2 * m + 1) + 77 := by
  apply refinement_cleared (k := 9) (r := 77) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_77]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 78). -/
theorem data_9_78 : oddCount 78 9 = 5 ∧
    acceleratedOrbit 9 78 = 38 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_78 : gap 9 78 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_78 : threshold 9 78 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_78 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 78) = 243 * (2 * m) + 38 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 78
  rw [data_9_78.1, data_9_78.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_78 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 78) = 243 * (2 * m + 1) + 38 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 78
  rw [data_9_78.1, data_9_78.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_78 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 78) < 512 * (2 * m) + 78 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 78 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_78] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 78) < 512 * (2 * m) + 78 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_78 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 78) < 512 * (2 * m + 1) + 78 := by
  apply refinement_cleared (k := 9) (r := 78) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_78]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 79). -/
theorem data_9_79 : oddCount 79 9 = 5 ∧
    acceleratedOrbit 9 79 = 38 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_79 : gap 9 79 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_79 : threshold 9 79 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_79 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 79) = 243 * (2 * m) + 38 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 79
  rw [data_9_79.1, data_9_79.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_79 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 79) = 243 * (2 * m + 1) + 38 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 79
  rw [data_9_79.1, data_9_79.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_79 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 79) < 512 * (2 * m) + 79 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 79 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_79] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 79) < 512 * (2 * m) + 79 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_79 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 79) < 512 * (2 * m + 1) + 79 := by
  apply refinement_cleared (k := 9) (r := 79) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_79]; decide

end Collatz.Research.RefinementAtlas.Batch157
