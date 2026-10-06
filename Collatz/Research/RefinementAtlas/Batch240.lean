import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 240. -/
namespace Collatz.Research.RefinementAtlas.Batch240
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 408). -/
theorem data_9_408 : oddCount 408 9 = 3 ∧
    acceleratedOrbit 9 408 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_408 : gap 9 408 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_408 : threshold 9 408 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_408 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 408) = 27 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 408
  rw [data_9_408.1, data_9_408.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_408 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 408) = 27 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 408
  rw [data_9_408.1, data_9_408.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_408 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 408) < 512 * (2 * m) + 408 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 408 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_408] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 408) < 512 * (2 * m) + 408 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_408 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 408) < 512 * (2 * m + 1) + 408 := by
  apply refinement_cleared (k := 9) (r := 408) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_408]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 409). -/
theorem data_9_409 : oddCount 409 9 = 4 ∧
    acceleratedOrbit 9 409 = 65 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_409 : gap 9 409 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_409 : threshold 9 409 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_409 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 409) = 81 * (2 * m) + 65 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 409
  rw [data_9_409.1, data_9_409.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_409 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 409) = 81 * (2 * m + 1) + 65 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 409
  rw [data_9_409.1, data_9_409.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_409 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 409) < 512 * (2 * m) + 409 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 409 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_409] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 409) < 512 * (2 * m) + 409 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_409 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 409) < 512 * (2 * m + 1) + 409 := by
  apply refinement_cleared (k := 9) (r := 409) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_409]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 410). -/
theorem data_9_410 : oddCount 410 9 = 3 ∧
    acceleratedOrbit 9 410 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_410 : gap 9 410 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_410 : threshold 9 410 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_410 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 410) = 27 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 410
  rw [data_9_410.1, data_9_410.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_410 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 410) = 27 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 410
  rw [data_9_410.1, data_9_410.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_410 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 410) < 512 * (2 * m) + 410 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 410 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_410] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 410) < 512 * (2 * m) + 410 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_410 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 410) < 512 * (2 * m + 1) + 410 := by
  apply refinement_cleared (k := 9) (r := 410) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_410]; decide

end Collatz.Research.RefinementAtlas.Batch240
