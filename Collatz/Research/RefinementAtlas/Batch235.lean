import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 235. -/
namespace Collatz.Research.RefinementAtlas.Batch235
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 391). -/
theorem data_9_391 : oddCount 391 9 = 4 ∧
    acceleratedOrbit 9 391 = 62 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_391 : gap 9 391 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_391 : threshold 9 391 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_391 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 391) = 81 * (2 * m) + 62 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 391
  rw [data_9_391.1, data_9_391.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_391 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 391) = 81 * (2 * m + 1) + 62 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 391
  rw [data_9_391.1, data_9_391.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_391 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 391) < 512 * (2 * m) + 391 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 391 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_391] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 391) < 512 * (2 * m) + 391 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_391 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 391) < 512 * (2 * m + 1) + 391 := by
  apply refinement_cleared (k := 9) (r := 391) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_391]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 392). -/
theorem data_9_392 : oddCount 392 9 = 2 ∧
    acceleratedOrbit 9 392 = 7 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_392 : gap 9 392 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_392 : threshold 9 392 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_392 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 392) = 9 * (2 * m) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 392
  rw [data_9_392.1, data_9_392.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_392 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 392) = 9 * (2 * m + 1) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 392
  rw [data_9_392.1, data_9_392.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_392 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 392) < 512 * (2 * m) + 392 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 392 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_392] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 392) < 512 * (2 * m) + 392 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_392 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 392) < 512 * (2 * m + 1) + 392 := by
  apply refinement_cleared (k := 9) (r := 392) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_392]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 394). -/
theorem data_9_394 : oddCount 394 9 = 2 ∧
    acceleratedOrbit 9 394 = 7 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_394 : gap 9 394 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_394 : threshold 9 394 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_394 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 394) = 9 * (2 * m) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 394
  rw [data_9_394.1, data_9_394.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_394 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 394) = 9 * (2 * m + 1) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 394
  rw [data_9_394.1, data_9_394.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_394 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 394) < 512 * (2 * m) + 394 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 394 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_394] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 394) < 512 * (2 * m) + 394 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_394 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 394) < 512 * (2 * m + 1) + 394 := by
  apply refinement_cleared (k := 9) (r := 394) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_394]; decide

end Collatz.Research.RefinementAtlas.Batch235
