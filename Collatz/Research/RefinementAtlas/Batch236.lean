import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 236. -/
namespace Collatz.Research.RefinementAtlas.Batch236
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 396). -/
theorem data_9_396 : oddCount 396 9 = 2 ∧
    acceleratedOrbit 9 396 = 7 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_396 : gap 9 396 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_396 : threshold 9 396 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_396 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 396) = 9 * (2 * m) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 396
  rw [data_9_396.1, data_9_396.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_396 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 396) = 9 * (2 * m + 1) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 396
  rw [data_9_396.1, data_9_396.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_396 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 396) < 512 * (2 * m) + 396 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 396 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_396] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 396) < 512 * (2 * m) + 396 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_396 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 396) < 512 * (2 * m + 1) + 396 := by
  apply refinement_cleared (k := 9) (r := 396) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_396]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 397). -/
theorem data_9_397 : oddCount 397 9 = 2 ∧
    acceleratedOrbit 9 397 = 7 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_397 : gap 9 397 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_397 : threshold 9 397 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_397 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 397) = 9 * (2 * m) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 397
  rw [data_9_397.1, data_9_397.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_397 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 397) = 9 * (2 * m + 1) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 397
  rw [data_9_397.1, data_9_397.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_397 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 397) < 512 * (2 * m) + 397 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 397 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_397] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 397) < 512 * (2 * m) + 397 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_397 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 397) < 512 * (2 * m + 1) + 397 := by
  apply refinement_cleared (k := 9) (r := 397) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_397]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 398). -/
theorem data_9_398 : oddCount 398 9 = 5 ∧
    acceleratedOrbit 9 398 = 190 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_398 : gap 9 398 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_398 : threshold 9 398 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_398 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 398) = 243 * (2 * m) + 190 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 398
  rw [data_9_398.1, data_9_398.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_398 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 398) = 243 * (2 * m + 1) + 190 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 398
  rw [data_9_398.1, data_9_398.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_398 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 398) < 512 * (2 * m) + 398 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 398 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_398] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 398) < 512 * (2 * m) + 398 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_398 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 398) < 512 * (2 * m + 1) + 398 := by
  apply refinement_cleared (k := 9) (r := 398) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_398]; decide

end Collatz.Research.RefinementAtlas.Batch236
