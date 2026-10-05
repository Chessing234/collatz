import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 247. -/
namespace Collatz.Research.RefinementAtlas.Batch247
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 437). -/
theorem data_9_437 : oddCount 437 9 = 4 ∧
    acceleratedOrbit 9 437 = 71 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_437 : gap 9 437 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_437 : threshold 9 437 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_437 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 437) = 81 * (2 * m) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 437
  rw [data_9_437.1, data_9_437.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_437 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 437) = 81 * (2 * m + 1) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 437
  rw [data_9_437.1, data_9_437.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_437 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 437) < 512 * (2 * m) + 437 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 437 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_437] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 437) < 512 * (2 * m) + 437 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_437 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 437) < 512 * (2 * m + 1) + 437 := by
  apply refinement_cleared (k := 9) (r := 437) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_437]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 438). -/
theorem data_9_438 : oddCount 438 9 = 5 ∧
    acceleratedOrbit 9 438 = 209 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_438 : gap 9 438 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_438 : threshold 9 438 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_438 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 438) = 243 * (2 * m) + 209 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 438
  rw [data_9_438.1, data_9_438.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_438 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 438) = 243 * (2 * m + 1) + 209 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 438
  rw [data_9_438.1, data_9_438.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_438 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 438) < 512 * (2 * m) + 438 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 438 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_438] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 438) < 512 * (2 * m) + 438 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_438 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 438) < 512 * (2 * m + 1) + 438 := by
  apply refinement_cleared (k := 9) (r := 438) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_438]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 439). -/
theorem data_9_439 : oddCount 439 9 = 5 ∧
    acceleratedOrbit 9 439 = 209 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_439 : gap 9 439 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_439 : threshold 9 439 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_439 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 439) = 243 * (2 * m) + 209 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 439
  rw [data_9_439.1, data_9_439.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_439 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 439) = 243 * (2 * m + 1) + 209 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 439
  rw [data_9_439.1, data_9_439.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_439 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 439) < 512 * (2 * m) + 439 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 439 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_439] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 439) < 512 * (2 * m) + 439 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_439 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 439) < 512 * (2 * m + 1) + 439 := by
  apply refinement_cleared (k := 9) (r := 439) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_439]; decide

end Collatz.Research.RefinementAtlas.Batch247
