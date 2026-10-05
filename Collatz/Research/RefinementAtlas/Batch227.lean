import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 227. -/
namespace Collatz.Research.RefinementAtlas.Batch227
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 362). -/
theorem data_9_362 : oddCount 362 9 = 3 ∧
    acceleratedOrbit 9 362 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_362 : gap 9 362 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_362 : threshold 9 362 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_362 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 362) = 27 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 362
  rw [data_9_362.1, data_9_362.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_362 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 362) = 27 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 362
  rw [data_9_362.1, data_9_362.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_362 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 362) < 512 * (2 * m) + 362 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 362 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_362] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 362) < 512 * (2 * m) + 362 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_362 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 362) < 512 * (2 * m + 1) + 362 := by
  apply refinement_cleared (k := 9) (r := 362) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_362]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 363). -/
theorem data_9_363 : oddCount 363 9 = 5 ∧
    acceleratedOrbit 9 363 = 173 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_363 : gap 9 363 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_363 : threshold 9 363 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_363 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 363) = 243 * (2 * m) + 173 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 363
  rw [data_9_363.1, data_9_363.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_363 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 363) = 243 * (2 * m + 1) + 173 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 363
  rw [data_9_363.1, data_9_363.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_363 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 363) < 512 * (2 * m) + 363 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 363 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_363] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 363) < 512 * (2 * m) + 363 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_363 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 363) < 512 * (2 * m + 1) + 363 := by
  apply refinement_cleared (k := 9) (r := 363) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_363]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 364). -/
theorem data_9_364 : oddCount 364 9 = 5 ∧
    acceleratedOrbit 9 364 = 175 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_364 : gap 9 364 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_364 : threshold 9 364 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_364 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 364) = 243 * (2 * m) + 175 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 364
  rw [data_9_364.1, data_9_364.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_364 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 364) = 243 * (2 * m + 1) + 175 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 364
  rw [data_9_364.1, data_9_364.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_364 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 364) < 512 * (2 * m) + 364 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 364 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_364] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 364) < 512 * (2 * m) + 364 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_364 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 364) < 512 * (2 * m + 1) + 364 := by
  apply refinement_cleared (k := 9) (r := 364) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_364]; decide

end Collatz.Research.RefinementAtlas.Batch227
