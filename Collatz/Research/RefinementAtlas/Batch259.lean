import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 259. -/
namespace Collatz.Research.RefinementAtlas.Batch259
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 492). -/
theorem data_9_492 : oddCount 492 9 = 5 ∧
    acceleratedOrbit 9 492 = 236 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_492 : gap 9 492 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_492 : threshold 9 492 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_492 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 492) = 243 * (2 * m) + 236 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 492
  rw [data_9_492.1, data_9_492.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_492 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 492) = 243 * (2 * m + 1) + 236 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 492
  rw [data_9_492.1, data_9_492.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_492 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 492) < 512 * (2 * m) + 492 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 492 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_492] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 492) < 512 * (2 * m) + 492 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_492 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 492) < 512 * (2 * m + 1) + 492 := by
  apply refinement_cleared (k := 9) (r := 492) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_492]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 493). -/
theorem data_9_493 : oddCount 493 9 = 5 ∧
    acceleratedOrbit 9 493 = 236 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_493 : gap 9 493 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_493 : threshold 9 493 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_493 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 493) = 243 * (2 * m) + 236 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 493
  rw [data_9_493.1, data_9_493.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_493 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 493) = 243 * (2 * m + 1) + 236 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 493
  rw [data_9_493.1, data_9_493.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_493 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 493) < 512 * (2 * m) + 493 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 493 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_493] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 493) < 512 * (2 * m) + 493 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_493 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 493) < 512 * (2 * m + 1) + 493 := by
  apply refinement_cleared (k := 9) (r := 493) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_493]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 494). -/
theorem data_9_494 : oddCount 494 9 = 5 ∧
    acceleratedOrbit 9 494 = 236 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_494 : gap 9 494 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_494 : threshold 9 494 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_494 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 494) = 243 * (2 * m) + 236 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 494
  rw [data_9_494.1, data_9_494.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_494 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 494) = 243 * (2 * m + 1) + 236 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 494
  rw [data_9_494.1, data_9_494.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_494 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 494) < 512 * (2 * m) + 494 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 494 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_494] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 494) < 512 * (2 * m) + 494 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_494 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 494) < 512 * (2 * m + 1) + 494 := by
  apply refinement_cleared (k := 9) (r := 494) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_494]; decide

end Collatz.Research.RefinementAtlas.Batch259
