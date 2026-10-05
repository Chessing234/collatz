import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 253. -/
namespace Collatz.Research.RefinementAtlas.Batch253
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 464). -/
theorem data_9_464 : oddCount 464 9 = 3 ∧
    acceleratedOrbit 9 464 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_464 : gap 9 464 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_464 : threshold 9 464 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_464 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 464) = 27 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 464
  rw [data_9_464.1, data_9_464.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_464 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 464) = 27 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 464
  rw [data_9_464.1, data_9_464.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_464 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 464) < 512 * (2 * m) + 464 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 464 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_464] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 464) < 512 * (2 * m) + 464 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_464 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 464) < 512 * (2 * m + 1) + 464 := by
  apply refinement_cleared (k := 9) (r := 464) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_464]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 465). -/
theorem data_9_465 : oddCount 465 9 = 4 ∧
    acceleratedOrbit 9 465 = 74 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_465 : gap 9 465 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_465 : threshold 9 465 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_465 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 465) = 81 * (2 * m) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 465
  rw [data_9_465.1, data_9_465.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_465 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 465) = 81 * (2 * m + 1) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 465
  rw [data_9_465.1, data_9_465.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_465 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 465) < 512 * (2 * m) + 465 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 465 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_465] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 465) < 512 * (2 * m) + 465 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_465 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 465) < 512 * (2 * m + 1) + 465 := by
  apply refinement_cleared (k := 9) (r := 465) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_465]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 468). -/
theorem data_9_468 : oddCount 468 9 = 3 ∧
    acceleratedOrbit 9 468 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_468 : gap 9 468 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_468 : threshold 9 468 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_468 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 468) = 27 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 468
  rw [data_9_468.1, data_9_468.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_468 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 468) = 27 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 468
  rw [data_9_468.1, data_9_468.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_468 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 468) < 512 * (2 * m) + 468 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 468 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_468] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 468) < 512 * (2 * m) + 468 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_468 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 468) < 512 * (2 * m + 1) + 468 := by
  apply refinement_cleared (k := 9) (r := 468) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_468]; decide

end Collatz.Research.RefinementAtlas.Batch253
