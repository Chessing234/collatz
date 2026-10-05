import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 202. -/
namespace Collatz.Research.RefinementAtlas.Batch202
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 264). -/
theorem data_9_264 : oddCount 264 9 = 4 ∧
    acceleratedOrbit 9 264 = 44 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_264 : gap 9 264 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_264 : threshold 9 264 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_264 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 264) = 81 * (2 * m) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 264
  rw [data_9_264.1, data_9_264.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_264 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 264) = 81 * (2 * m + 1) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 264
  rw [data_9_264.1, data_9_264.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_264 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 264) < 512 * (2 * m) + 264 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 264 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_264] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 264) < 512 * (2 * m) + 264 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_264 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 264) < 512 * (2 * m + 1) + 264 := by
  apply refinement_cleared (k := 9) (r := 264) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_264]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 266). -/
theorem data_9_266 : oddCount 266 9 = 4 ∧
    acceleratedOrbit 9 266 = 44 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_266 : gap 9 266 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_266 : threshold 9 266 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_266 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 266) = 81 * (2 * m) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 266
  rw [data_9_266.1, data_9_266.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_266 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 266) = 81 * (2 * m + 1) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 266
  rw [data_9_266.1, data_9_266.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_266 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 266) < 512 * (2 * m) + 266 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 266 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_266] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 266) < 512 * (2 * m) + 266 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_266 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 266) < 512 * (2 * m + 1) + 266 := by
  apply refinement_cleared (k := 9) (r := 266) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_266]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 267). -/
theorem data_9_267 : oddCount 267 9 = 5 ∧
    acceleratedOrbit 9 267 = 128 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_267 : gap 9 267 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_267 : threshold 9 267 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_267 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 267) = 243 * (2 * m) + 128 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 267
  rw [data_9_267.1, data_9_267.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_267 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 267) = 243 * (2 * m + 1) + 128 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 267
  rw [data_9_267.1, data_9_267.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_267 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 267) < 512 * (2 * m) + 267 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 267 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_267] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 267) < 512 * (2 * m) + 267 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_267 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 267) < 512 * (2 * m + 1) + 267 := by
  apply refinement_cleared (k := 9) (r := 267) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_267]; decide

end Collatz.Research.RefinementAtlas.Batch202
