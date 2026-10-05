import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 244. -/
namespace Collatz.Research.RefinementAtlas.Batch244
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 428). -/
theorem data_9_428 : oddCount 428 9 = 5 ∧
    acceleratedOrbit 9 428 = 206 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_428 : gap 9 428 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_428 : threshold 9 428 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_428 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 428) = 243 * (2 * m) + 206 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 428
  rw [data_9_428.1, data_9_428.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_428 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 428) = 243 * (2 * m + 1) + 206 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 428
  rw [data_9_428.1, data_9_428.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_428 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 428) < 512 * (2 * m) + 428 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 428 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_428] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 428) < 512 * (2 * m) + 428 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_428 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 428) < 512 * (2 * m + 1) + 428 := by
  apply refinement_cleared (k := 9) (r := 428) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_428]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 429). -/
theorem data_9_429 : oddCount 429 9 = 5 ∧
    acceleratedOrbit 9 429 = 206 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_429 : gap 9 429 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_429 : threshold 9 429 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_429 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 429) = 243 * (2 * m) + 206 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 429
  rw [data_9_429.1, data_9_429.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_429 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 429) = 243 * (2 * m + 1) + 206 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 429
  rw [data_9_429.1, data_9_429.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_429 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 429) < 512 * (2 * m) + 429 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 429 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_429] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 429) < 512 * (2 * m) + 429 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_429 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 429) < 512 * (2 * m + 1) + 429 := by
  apply refinement_cleared (k := 9) (r := 429) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_429]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 430). -/
theorem data_9_430 : oddCount 430 9 = 5 ∧
    acceleratedOrbit 9 430 = 206 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_430 : gap 9 430 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_430 : threshold 9 430 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_430 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 430) = 243 * (2 * m) + 206 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 430
  rw [data_9_430.1, data_9_430.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_430 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 430) = 243 * (2 * m + 1) + 206 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 430
  rw [data_9_430.1, data_9_430.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_430 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 430) < 512 * (2 * m) + 430 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 430 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_430] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 430) < 512 * (2 * m) + 430 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_430 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 430) < 512 * (2 * m + 1) + 430 := by
  apply refinement_cleared (k := 9) (r := 430) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_430]; decide

end Collatz.Research.RefinementAtlas.Batch244
