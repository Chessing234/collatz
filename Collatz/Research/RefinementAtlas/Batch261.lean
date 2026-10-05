import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 261. -/
namespace Collatz.Research.RefinementAtlas.Batch261
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 499). -/
theorem data_9_499 : oddCount 499 9 = 5 ∧
    acceleratedOrbit 9 499 = 238 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_499 : gap 9 499 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_499 : threshold 9 499 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_499 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 499) = 243 * (2 * m) + 238 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 499
  rw [data_9_499.1, data_9_499.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_499 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 499) = 243 * (2 * m + 1) + 238 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 499
  rw [data_9_499.1, data_9_499.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_499 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 499) < 512 * (2 * m) + 499 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 499 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_499] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 499) < 512 * (2 * m) + 499 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_499 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 499) < 512 * (2 * m + 1) + 499 := by
  apply refinement_cleared (k := 9) (r := 499) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_499]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 500). -/
theorem data_9_500 : oddCount 500 9 = 5 ∧
    acceleratedOrbit 9 500 = 242 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_500 : gap 9 500 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_500 : threshold 9 500 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_500 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 500) = 243 * (2 * m) + 242 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 500
  rw [data_9_500.1, data_9_500.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_500 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 500) = 243 * (2 * m + 1) + 242 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 500
  rw [data_9_500.1, data_9_500.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_500 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 500) < 512 * (2 * m) + 500 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 500 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_500] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 500) < 512 * (2 * m) + 500 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_500 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 500) < 512 * (2 * m + 1) + 500 := by
  apply refinement_cleared (k := 9) (r := 500) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_500]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 501). -/
theorem data_9_501 : oddCount 501 9 = 5 ∧
    acceleratedOrbit 9 501 = 242 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_501 : gap 9 501 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_501 : threshold 9 501 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_501 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 501) = 243 * (2 * m) + 242 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 501
  rw [data_9_501.1, data_9_501.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_501 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 501) = 243 * (2 * m + 1) + 242 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 501
  rw [data_9_501.1, data_9_501.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_501 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 501) < 512 * (2 * m) + 501 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 501 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_501] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 501) < 512 * (2 * m) + 501 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_501 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 501) < 512 * (2 * m + 1) + 501 := by
  apply refinement_cleared (k := 9) (r := 501) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_501]; decide

end Collatz.Research.RefinementAtlas.Batch261
