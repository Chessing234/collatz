import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 224. -/
namespace Collatz.Research.RefinementAtlas.Batch224
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 351). -/
theorem data_9_351 : oddCount 351 9 = 5 ∧
    acceleratedOrbit 9 351 = 167 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_351 : gap 9 351 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_351 : threshold 9 351 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_351 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 351) = 243 * (2 * m) + 167 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 351
  rw [data_9_351.1, data_9_351.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_351 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 351) = 243 * (2 * m + 1) + 167 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 351
  rw [data_9_351.1, data_9_351.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_351 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 351) < 512 * (2 * m) + 351 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 351 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_351] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 351) < 512 * (2 * m) + 351 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_351 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 351) < 512 * (2 * m + 1) + 351 := by
  apply refinement_cleared (k := 9) (r := 351) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_351]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 352). -/
theorem data_9_352 : oddCount 352 9 = 3 ∧
    acceleratedOrbit 9 352 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_352 : gap 9 352 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_352 : threshold 9 352 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_352 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 352) = 27 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 352
  rw [data_9_352.1, data_9_352.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_352 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 352) = 27 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 352
  rw [data_9_352.1, data_9_352.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_352 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 352) < 512 * (2 * m) + 352 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 352 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_352] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 352) < 512 * (2 * m) + 352 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_352 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 352) < 512 * (2 * m + 1) + 352 := by
  apply refinement_cleared (k := 9) (r := 352) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_352]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 354). -/
theorem data_9_354 : oddCount 354 9 = 3 ∧
    acceleratedOrbit 9 354 = 19 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_354 : gap 9 354 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_354 : threshold 9 354 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_354 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 354) = 27 * (2 * m) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 354
  rw [data_9_354.1, data_9_354.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_354 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 354) = 27 * (2 * m + 1) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 354
  rw [data_9_354.1, data_9_354.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_354 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 354) < 512 * (2 * m) + 354 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 354 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_354] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 354) < 512 * (2 * m) + 354 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_354 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 354) < 512 * (2 * m + 1) + 354 := by
  apply refinement_cleared (k := 9) (r := 354) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_354]; decide

end Collatz.Research.RefinementAtlas.Batch224
