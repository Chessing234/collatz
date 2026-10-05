import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 229. -/
namespace Collatz.Research.RefinementAtlas.Batch229
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 369). -/
theorem data_9_369 : oddCount 369 9 = 3 ∧
    acceleratedOrbit 9 369 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_369 : gap 9 369 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_369 : threshold 9 369 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_369 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 369) = 27 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 369
  rw [data_9_369.1, data_9_369.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_369 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 369) = 27 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 369
  rw [data_9_369.1, data_9_369.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_369 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 369) < 512 * (2 * m) + 369 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 369 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_369] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 369) < 512 * (2 * m) + 369 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_369 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 369) < 512 * (2 * m + 1) + 369 := by
  apply refinement_cleared (k := 9) (r := 369) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_369]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 370). -/
theorem data_9_370 : oddCount 370 9 = 4 ∧
    acceleratedOrbit 9 370 = 59 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_370 : gap 9 370 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_370 : threshold 9 370 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_370 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 370) = 81 * (2 * m) + 59 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 370
  rw [data_9_370.1, data_9_370.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_370 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 370) = 81 * (2 * m + 1) + 59 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 370
  rw [data_9_370.1, data_9_370.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_370 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 370) < 512 * (2 * m) + 370 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 370 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_370] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 370) < 512 * (2 * m) + 370 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_370 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 370) < 512 * (2 * m + 1) + 370 := by
  apply refinement_cleared (k := 9) (r := 370) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_370]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 371). -/
theorem data_9_371 : oddCount 371 9 = 4 ∧
    acceleratedOrbit 9 371 = 59 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_371 : gap 9 371 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_371 : threshold 9 371 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_371 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 371) = 81 * (2 * m) + 59 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 371
  rw [data_9_371.1, data_9_371.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_371 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 371) = 81 * (2 * m + 1) + 59 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 371
  rw [data_9_371.1, data_9_371.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_371 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 371) < 512 * (2 * m) + 371 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 371 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_371] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 371) < 512 * (2 * m) + 371 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_371 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 371) < 512 * (2 * m + 1) + 371 := by
  apply refinement_cleared (k := 9) (r := 371) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_371]; decide

end Collatz.Research.RefinementAtlas.Batch229
