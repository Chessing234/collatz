import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 210. -/
namespace Collatz.Research.RefinementAtlas.Batch210
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 294). -/
theorem data_9_294 : oddCount 294 9 = 4 ∧
    acceleratedOrbit 9 294 = 47 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_294 : gap 9 294 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_294 : threshold 9 294 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_294 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 294) = 81 * (2 * m) + 47 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 294
  rw [data_9_294.1, data_9_294.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_294 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 294) = 81 * (2 * m + 1) + 47 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 294
  rw [data_9_294.1, data_9_294.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_294 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 294) < 512 * (2 * m) + 294 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 294 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_294] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 294) < 512 * (2 * m) + 294 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_294 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 294) < 512 * (2 * m + 1) + 294 := by
  apply refinement_cleared (k := 9) (r := 294) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_294]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 296). -/
theorem data_9_296 : oddCount 296 9 = 3 ∧
    acceleratedOrbit 9 296 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_296 : gap 9 296 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_296 : threshold 9 296 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_296 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 296) = 27 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 296
  rw [data_9_296.1, data_9_296.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_296 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 296) = 27 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 296
  rw [data_9_296.1, data_9_296.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_296 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 296) < 512 * (2 * m) + 296 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 296 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_296] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 296) < 512 * (2 * m) + 296 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_296 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 296) < 512 * (2 * m + 1) + 296 := by
  apply refinement_cleared (k := 9) (r := 296) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_296]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 298). -/
theorem data_9_298 : oddCount 298 9 = 3 ∧
    acceleratedOrbit 9 298 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_298 : gap 9 298 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_298 : threshold 9 298 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_298 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 298) = 27 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 298
  rw [data_9_298.1, data_9_298.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_298 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 298) = 27 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 298
  rw [data_9_298.1, data_9_298.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_298 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 298) < 512 * (2 * m) + 298 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 298 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_298] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 298) < 512 * (2 * m) + 298 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_298 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 298) < 512 * (2 * m + 1) + 298 := by
  apply refinement_cleared (k := 9) (r := 298) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_298]; decide

end Collatz.Research.RefinementAtlas.Batch210
