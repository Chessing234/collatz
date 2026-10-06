import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 218. -/
namespace Collatz.Research.RefinementAtlas.Batch218
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 326). -/
theorem data_9_326 : oddCount 326 9 = 4 ∧
    acceleratedOrbit 9 326 = 53 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_326 : gap 9 326 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_326 : threshold 9 326 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_326 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 326) = 81 * (2 * m) + 53 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 326
  rw [data_9_326.1, data_9_326.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_326 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 326) = 81 * (2 * m + 1) + 53 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 326
  rw [data_9_326.1, data_9_326.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_326 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 326) < 512 * (2 * m) + 326 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 326 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_326] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 326) < 512 * (2 * m) + 326 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_326 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 326) < 512 * (2 * m + 1) + 326 := by
  apply refinement_cleared (k := 9) (r := 326) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_326]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 328). -/
theorem data_9_328 : oddCount 328 9 = 5 ∧
    acceleratedOrbit 9 328 = 161 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_328 : gap 9 328 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_328 : threshold 9 328 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_328 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 328) = 243 * (2 * m) + 161 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 328
  rw [data_9_328.1, data_9_328.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_328 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 328) = 243 * (2 * m + 1) + 161 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 328
  rw [data_9_328.1, data_9_328.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_328 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 328) < 512 * (2 * m) + 328 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 328 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_328] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 328) < 512 * (2 * m) + 328 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_328 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 328) < 512 * (2 * m + 1) + 328 := by
  apply refinement_cleared (k := 9) (r := 328) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_328]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 329). -/
theorem data_9_329 : oddCount 329 9 = 5 ∧
    acceleratedOrbit 9 329 = 157 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_329 : gap 9 329 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_329 : threshold 9 329 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_329 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 329) = 243 * (2 * m) + 157 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 329
  rw [data_9_329.1, data_9_329.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_329 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 329) = 243 * (2 * m + 1) + 157 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 329
  rw [data_9_329.1, data_9_329.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_329 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 329) < 512 * (2 * m) + 329 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 329 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_329] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 329) < 512 * (2 * m) + 329 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_329 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 329) < 512 * (2 * m + 1) + 329 := by
  apply refinement_cleared (k := 9) (r := 329) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_329]; decide

end Collatz.Research.RefinementAtlas.Batch218
