import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 144. -/
namespace Collatz.Research.RefinementAtlas.Batch144
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 29). -/
theorem data_9_29 : oddCount 29 9 = 4 ∧
    acceleratedOrbit 9 29 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_29 : gap 9 29 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_29 : threshold 9 29 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_29 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 29) = 81 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 29
  rw [data_9_29.1, data_9_29.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_29 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 29) = 81 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 29
  rw [data_9_29.1, data_9_29.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_29 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 29) < 512 * (2 * m) + 29 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 29 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_29] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 29) < 512 * (2 * m) + 29 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_29 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 29) < 512 * (2 * m + 1) + 29 := by
  apply refinement_cleared (k := 9) (r := 29) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_29]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 30). -/
theorem data_9_30 : oddCount 30 9 = 4 ∧
    acceleratedOrbit 9 30 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_30 : gap 9 30 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_30 : threshold 9 30 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_30 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 30) = 81 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 30
  rw [data_9_30.1, data_9_30.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_30 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 30) = 81 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 30
  rw [data_9_30.1, data_9_30.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_30 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 30) < 512 * (2 * m) + 30 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 30 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_30] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 30) < 512 * (2 * m) + 30 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_30 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 30) < 512 * (2 * m + 1) + 30 := by
  apply refinement_cleared (k := 9) (r := 30) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_30]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 32). -/
theorem data_9_32 : oddCount 32 9 = 2 ∧
    acceleratedOrbit 9 32 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_32 : gap 9 32 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_32 : threshold 9 32 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_32 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 32) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 32
  rw [data_9_32.1, data_9_32.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_32 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 32) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 32
  rw [data_9_32.1, data_9_32.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_32 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 32) < 512 * (2 * m) + 32 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 32 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_32] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 32) < 512 * (2 * m) + 32 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_32 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 32) < 512 * (2 * m + 1) + 32 := by
  apply refinement_cleared (k := 9) (r := 32) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_32]; decide

end Collatz.Research.RefinementAtlas.Batch144
