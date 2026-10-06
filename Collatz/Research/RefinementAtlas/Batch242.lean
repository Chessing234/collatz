import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 242. -/
namespace Collatz.Research.RefinementAtlas.Batch242
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 419). -/
theorem data_9_419 : oddCount 419 9 = 4 ∧
    acceleratedOrbit 9 419 = 67 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_419 : gap 9 419 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_419 : threshold 9 419 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_419 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 419) = 81 * (2 * m) + 67 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 419
  rw [data_9_419.1, data_9_419.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_419 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 419) = 81 * (2 * m + 1) + 67 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 419
  rw [data_9_419.1, data_9_419.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_419 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 419) < 512 * (2 * m) + 419 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 419 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_419] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 419) < 512 * (2 * m) + 419 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_419 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 419) < 512 * (2 * m + 1) + 419 := by
  apply refinement_cleared (k := 9) (r := 419) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_419]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 420). -/
theorem data_9_420 : oddCount 420 9 = 5 ∧
    acceleratedOrbit 9 420 = 202 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_420 : gap 9 420 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_420 : threshold 9 420 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_420 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 420) = 243 * (2 * m) + 202 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 420
  rw [data_9_420.1, data_9_420.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_420 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 420) = 243 * (2 * m + 1) + 202 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 420
  rw [data_9_420.1, data_9_420.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_420 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 420) < 512 * (2 * m) + 420 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 420 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_420] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 420) < 512 * (2 * m) + 420 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_420 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 420) < 512 * (2 * m + 1) + 420 := by
  apply refinement_cleared (k := 9) (r := 420) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_420]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 421). -/
theorem data_9_421 : oddCount 421 9 = 5 ∧
    acceleratedOrbit 9 421 = 202 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_421 : gap 9 421 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_421 : threshold 9 421 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_421 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 421) = 243 * (2 * m) + 202 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 421
  rw [data_9_421.1, data_9_421.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_421 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 421) = 243 * (2 * m + 1) + 202 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 421
  rw [data_9_421.1, data_9_421.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_421 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 421) < 512 * (2 * m) + 421 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 421 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_421] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 421) < 512 * (2 * m) + 421 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_421 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 421) < 512 * (2 * m + 1) + 421 := by
  apply refinement_cleared (k := 9) (r := 421) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_421]; decide

end Collatz.Research.RefinementAtlas.Batch242
