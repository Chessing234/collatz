import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 241. -/
namespace Collatz.Research.RefinementAtlas.Batch241
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 416). -/
theorem data_9_416 : oddCount 416 9 = 2 ∧
    acceleratedOrbit 9 416 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_416 : gap 9 416 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_416 : threshold 9 416 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_416 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 416) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 416
  rw [data_9_416.1, data_9_416.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_416 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 416) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 416
  rw [data_9_416.1, data_9_416.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_416 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 416) < 512 * (2 * m) + 416 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 416 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_416] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 416) < 512 * (2 * m) + 416 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_416 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 416) < 512 * (2 * m + 1) + 416 := by
  apply refinement_cleared (k := 9) (r := 416) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_416]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 417). -/
theorem data_9_417 : oddCount 417 9 = 5 ∧
    acceleratedOrbit 9 417 = 199 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_417 : gap 9 417 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_417 : threshold 9 417 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_417 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 417) = 243 * (2 * m) + 199 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 417
  rw [data_9_417.1, data_9_417.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_417 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 417) = 243 * (2 * m + 1) + 199 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 417
  rw [data_9_417.1, data_9_417.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_417 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 417) < 512 * (2 * m) + 417 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 417 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_417] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 417) < 512 * (2 * m) + 417 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_417 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 417) < 512 * (2 * m + 1) + 417 := by
  apply refinement_cleared (k := 9) (r := 417) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_417]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 418). -/
theorem data_9_418 : oddCount 418 9 = 4 ∧
    acceleratedOrbit 9 418 = 67 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_418 : gap 9 418 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_418 : threshold 9 418 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_418 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 418) = 81 * (2 * m) + 67 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 418
  rw [data_9_418.1, data_9_418.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_418 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 418) = 81 * (2 * m + 1) + 67 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 418
  rw [data_9_418.1, data_9_418.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_418 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 418) < 512 * (2 * m) + 418 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 418 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_418] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 418) < 512 * (2 * m) + 418 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_418 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 418) < 512 * (2 * m + 1) + 418 := by
  apply refinement_cleared (k := 9) (r := 418) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_418]; decide

end Collatz.Research.RefinementAtlas.Batch241
