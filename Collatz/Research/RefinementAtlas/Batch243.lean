import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 243. -/
namespace Collatz.Research.RefinementAtlas.Batch243
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 422). -/
theorem data_9_422 : oddCount 422 9 = 5 ∧
    acceleratedOrbit 9 422 = 202 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_422 : gap 9 422 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_422 : threshold 9 422 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_422 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 422) = 243 * (2 * m) + 202 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 422
  rw [data_9_422.1, data_9_422.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_422 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 422) = 243 * (2 * m + 1) + 202 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 422
  rw [data_9_422.1, data_9_422.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_422 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 422) < 512 * (2 * m) + 422 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 422 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_422] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 422) < 512 * (2 * m) + 422 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_422 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 422) < 512 * (2 * m + 1) + 422 := by
  apply refinement_cleared (k := 9) (r := 422) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_422]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 424). -/
theorem data_9_424 : oddCount 424 9 = 2 ∧
    acceleratedOrbit 9 424 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_424 : gap 9 424 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_424 : threshold 9 424 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_424 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 424) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 424
  rw [data_9_424.1, data_9_424.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_424 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 424) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 424
  rw [data_9_424.1, data_9_424.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_424 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 424) < 512 * (2 * m) + 424 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 424 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_424] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 424) < 512 * (2 * m) + 424 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_424 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 424) < 512 * (2 * m + 1) + 424 := by
  apply refinement_cleared (k := 9) (r := 424) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_424]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 426). -/
theorem data_9_426 : oddCount 426 9 = 2 ∧
    acceleratedOrbit 9 426 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_426 : gap 9 426 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_426 : threshold 9 426 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_426 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 426) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 426
  rw [data_9_426.1, data_9_426.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_426 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 426) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 426
  rw [data_9_426.1, data_9_426.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_426 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 426) < 512 * (2 * m) + 426 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 426 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_426] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 426) < 512 * (2 * m) + 426 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_426 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 426) < 512 * (2 * m + 1) + 426 := by
  apply refinement_cleared (k := 9) (r := 426) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_426]; decide

end Collatz.Research.RefinementAtlas.Batch243
