import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 221. -/
namespace Collatz.Research.RefinementAtlas.Batch221
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 341). -/
theorem data_9_341 : oddCount 341 9 = 1 ∧
    acceleratedOrbit 9 341 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_341 : gap 9 341 = 509 ∧ 3 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_341 : threshold 9 341 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_341 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 341) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 341
  rw [data_9_341.1, data_9_341.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_341 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 341) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 341
  rw [data_9_341.1, data_9_341.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_341 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 341) < 512 * (2 * m) + 341 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 341 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_341] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 341) < 512 * (2 * m) + 341 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_341 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 341) < 512 * (2 * m + 1) + 341 := by
  apply refinement_cleared (k := 9) (r := 341) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_341]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 342). -/
theorem data_9_342 : oddCount 342 9 = 5 ∧
    acceleratedOrbit 9 342 = 164 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_342 : gap 9 342 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_342 : threshold 9 342 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_342 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 342) = 243 * (2 * m) + 164 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 342
  rw [data_9_342.1, data_9_342.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_342 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 342) = 243 * (2 * m + 1) + 164 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 342
  rw [data_9_342.1, data_9_342.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_342 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 342) < 512 * (2 * m) + 342 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 342 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_342] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 342) < 512 * (2 * m) + 342 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_342 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 342) < 512 * (2 * m + 1) + 342 := by
  apply refinement_cleared (k := 9) (r := 342) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_342]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 343). -/
theorem data_9_343 : oddCount 343 9 = 5 ∧
    acceleratedOrbit 9 343 = 164 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_343 : gap 9 343 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_343 : threshold 9 343 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_343 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 343) = 243 * (2 * m) + 164 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 343
  rw [data_9_343.1, data_9_343.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_343 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 343) = 243 * (2 * m + 1) + 164 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 343
  rw [data_9_343.1, data_9_343.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_343 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 343) < 512 * (2 * m) + 343 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 343 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_343] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 343) < 512 * (2 * m) + 343 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_343 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 343) < 512 * (2 * m + 1) + 343 := by
  apply refinement_cleared (k := 9) (r := 343) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_343]; decide

end Collatz.Research.RefinementAtlas.Batch221
