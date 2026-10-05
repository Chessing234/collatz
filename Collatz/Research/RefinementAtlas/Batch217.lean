import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 217. -/
namespace Collatz.Research.RefinementAtlas.Batch217
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 323). -/
theorem data_9_323 : oddCount 323 9 = 5 ∧
    acceleratedOrbit 9 323 = 155 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_323 : gap 9 323 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_323 : threshold 9 323 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_323 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 323) = 243 * (2 * m) + 155 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 323
  rw [data_9_323.1, data_9_323.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_323 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 323) = 243 * (2 * m + 1) + 155 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 323
  rw [data_9_323.1, data_9_323.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_323 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 323) < 512 * (2 * m) + 323 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 323 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_323] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 323) < 512 * (2 * m) + 323 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_323 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 323) < 512 * (2 * m + 1) + 323 := by
  apply refinement_cleared (k := 9) (r := 323) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_323]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 324). -/
theorem data_9_324 : oddCount 324 9 = 4 ∧
    acceleratedOrbit 9 324 = 53 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_324 : gap 9 324 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_324 : threshold 9 324 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_324 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 324) = 81 * (2 * m) + 53 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 324
  rw [data_9_324.1, data_9_324.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_324 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 324) = 81 * (2 * m + 1) + 53 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 324
  rw [data_9_324.1, data_9_324.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_324 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 324) < 512 * (2 * m) + 324 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 324 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_324] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 324) < 512 * (2 * m) + 324 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_324 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 324) < 512 * (2 * m + 1) + 324 := by
  apply refinement_cleared (k := 9) (r := 324) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_324]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 325). -/
theorem data_9_325 : oddCount 325 9 = 4 ∧
    acceleratedOrbit 9 325 = 53 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_325 : gap 9 325 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_325 : threshold 9 325 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_325 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 325) = 81 * (2 * m) + 53 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 325
  rw [data_9_325.1, data_9_325.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_325 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 325) = 81 * (2 * m + 1) + 53 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 325
  rw [data_9_325.1, data_9_325.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_325 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 325) < 512 * (2 * m) + 325 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 325 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_325] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 325) < 512 * (2 * m) + 325 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_325 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 325) < 512 * (2 * m + 1) + 325 := by
  apply refinement_cleared (k := 9) (r := 325) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_325]; decide

end Collatz.Research.RefinementAtlas.Batch217
