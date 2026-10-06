import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 257. -/
namespace Collatz.Research.RefinementAtlas.Batch257
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 483). -/
theorem data_9_483 : oddCount 483 9 = 3 ∧
    acceleratedOrbit 9 483 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_483 : gap 9 483 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_483 : threshold 9 483 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_483 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 483) = 27 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 483
  rw [data_9_483.1, data_9_483.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_483 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 483) = 27 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 483
  rw [data_9_483.1, data_9_483.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_483 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 483) < 512 * (2 * m) + 483 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 483 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_483] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 483) < 512 * (2 * m) + 483 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_483 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 483) < 512 * (2 * m + 1) + 483 := by
  apply refinement_cleared (k := 9) (r := 483) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_483]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 484). -/
theorem data_9_484 : oddCount 484 9 = 5 ∧
    acceleratedOrbit 9 484 = 233 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_484 : gap 9 484 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_484 : threshold 9 484 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_484 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 484) = 243 * (2 * m) + 233 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 484
  rw [data_9_484.1, data_9_484.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_484 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 484) = 243 * (2 * m + 1) + 233 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 484
  rw [data_9_484.1, data_9_484.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_484 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 484) < 512 * (2 * m) + 484 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 484 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_484] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 484) < 512 * (2 * m) + 484 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_484 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 484) < 512 * (2 * m + 1) + 484 := by
  apply refinement_cleared (k := 9) (r := 484) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_484]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 485). -/
theorem data_9_485 : oddCount 485 9 = 5 ∧
    acceleratedOrbit 9 485 = 233 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_485 : gap 9 485 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_485 : threshold 9 485 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_485 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 485) = 243 * (2 * m) + 233 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 485
  rw [data_9_485.1, data_9_485.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_485 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 485) = 243 * (2 * m + 1) + 233 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 485
  rw [data_9_485.1, data_9_485.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_485 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 485) < 512 * (2 * m) + 485 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 485 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_485] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 485) < 512 * (2 * m) + 485 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_485 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 485) < 512 * (2 * m + 1) + 485 := by
  apply refinement_cleared (k := 9) (r := 485) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_485]; decide

end Collatz.Research.RefinementAtlas.Batch257
