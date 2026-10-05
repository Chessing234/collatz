import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 226. -/
namespace Collatz.Research.RefinementAtlas.Batch226
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 358). -/
theorem data_9_358 : oddCount 358 9 = 3 ∧
    acceleratedOrbit 9 358 = 19 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_358 : gap 9 358 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_358 : threshold 9 358 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_358 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 358) = 27 * (2 * m) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 358
  rw [data_9_358.1, data_9_358.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_358 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 358) = 27 * (2 * m + 1) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 358
  rw [data_9_358.1, data_9_358.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_358 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 358) < 512 * (2 * m) + 358 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 358 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_358] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 358) < 512 * (2 * m) + 358 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_358 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 358) < 512 * (2 * m + 1) + 358 := by
  apply refinement_cleared (k := 9) (r := 358) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_358]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 360). -/
theorem data_9_360 : oddCount 360 9 = 3 ∧
    acceleratedOrbit 9 360 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_360 : gap 9 360 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_360 : threshold 9 360 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_360 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 360) = 27 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 360
  rw [data_9_360.1, data_9_360.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_360 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 360) = 27 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 360
  rw [data_9_360.1, data_9_360.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_360 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 360) < 512 * (2 * m) + 360 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 360 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_360] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 360) < 512 * (2 * m) + 360 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_360 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 360) < 512 * (2 * m + 1) + 360 := by
  apply refinement_cleared (k := 9) (r := 360) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_360]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 361). -/
theorem data_9_361 : oddCount 361 9 = 5 ∧
    acceleratedOrbit 9 361 = 172 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_361 : gap 9 361 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_361 : threshold 9 361 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_361 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 361) = 243 * (2 * m) + 172 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 361
  rw [data_9_361.1, data_9_361.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_361 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 361) = 243 * (2 * m + 1) + 172 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 361
  rw [data_9_361.1, data_9_361.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_361 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 361) < 512 * (2 * m) + 361 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 361 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_361] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 361) < 512 * (2 * m) + 361 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_361 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 361) < 512 * (2 * m + 1) + 361 := by
  apply refinement_cleared (k := 9) (r := 361) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_361]; decide

end Collatz.Research.RefinementAtlas.Batch226
