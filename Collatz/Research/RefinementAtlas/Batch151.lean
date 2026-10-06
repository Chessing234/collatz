import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 151. -/
namespace Collatz.Research.RefinementAtlas.Batch151
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 53). -/
theorem data_9_53 : oddCount 53 9 = 2 ∧
    acceleratedOrbit 9 53 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_53 : gap 9 53 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_53 : threshold 9 53 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_53 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 53) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 53
  rw [data_9_53.1, data_9_53.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_53 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 53) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 53
  rw [data_9_53.1, data_9_53.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_53 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 53) < 512 * (2 * m) + 53 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 53 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_53] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 53) < 512 * (2 * m) + 53 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_53 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 53) < 512 * (2 * m + 1) + 53 := by
  apply refinement_cleared (k := 9) (r := 53) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_53]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 56). -/
theorem data_9_56 : oddCount 56 9 = 4 ∧
    acceleratedOrbit 9 56 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_56 : gap 9 56 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_56 : threshold 9 56 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_56 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 56) = 81 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 56
  rw [data_9_56.1, data_9_56.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_56 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 56) = 81 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 56
  rw [data_9_56.1, data_9_56.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_56 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 56) < 512 * (2 * m) + 56 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 56 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_56] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 56) < 512 * (2 * m) + 56 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_56 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 56) < 512 * (2 * m + 1) + 56 := by
  apply refinement_cleared (k := 9) (r := 56) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_56]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 57). -/
theorem data_9_57 : oddCount 57 9 = 5 ∧
    acceleratedOrbit 9 57 = 28 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_57 : gap 9 57 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_57 : threshold 9 57 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_57 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 57) = 243 * (2 * m) + 28 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 57
  rw [data_9_57.1, data_9_57.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_57 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 57) = 243 * (2 * m + 1) + 28 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 57
  rw [data_9_57.1, data_9_57.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_57 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 57) < 512 * (2 * m) + 57 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 57 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_57] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 57) < 512 * (2 * m) + 57 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_57 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 57) < 512 * (2 * m + 1) + 57 := by
  apply refinement_cleared (k := 9) (r := 57) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_57]; decide

end Collatz.Research.RefinementAtlas.Batch151
