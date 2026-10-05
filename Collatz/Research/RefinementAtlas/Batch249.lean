import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 249. -/
namespace Collatz.Research.RefinementAtlas.Batch249
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 443). -/
theorem data_9_443 : oddCount 443 9 = 5 ∧
    acceleratedOrbit 9 443 = 211 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_443 : gap 9 443 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_443 : threshold 9 443 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_443 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 443) = 243 * (2 * m) + 211 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 443
  rw [data_9_443.1, data_9_443.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_443 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 443) = 243 * (2 * m + 1) + 211 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 443
  rw [data_9_443.1, data_9_443.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_443 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 443) < 512 * (2 * m) + 443 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 443 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_443] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 443) < 512 * (2 * m) + 443 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_443 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 443) < 512 * (2 * m + 1) + 443 := by
  apply refinement_cleared (k := 9) (r := 443) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_443]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 448). -/
theorem data_9_448 : oddCount 448 9 = 3 ∧
    acceleratedOrbit 9 448 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_448 : gap 9 448 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_448 : threshold 9 448 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_448 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 448) = 27 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 448
  rw [data_9_448.1, data_9_448.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_448 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 448) = 27 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 448
  rw [data_9_448.1, data_9_448.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_448 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 448) < 512 * (2 * m) + 448 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 448 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_448] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 448) < 512 * (2 * m) + 448 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_448 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 448) < 512 * (2 * m + 1) + 448 := by
  apply refinement_cleared (k := 9) (r := 448) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_448]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 449). -/
theorem data_9_449 : oddCount 449 9 = 5 ∧
    acceleratedOrbit 9 449 = 215 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_449 : gap 9 449 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_449 : threshold 9 449 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_449 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 449) = 243 * (2 * m) + 215 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 449
  rw [data_9_449.1, data_9_449.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_449 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 449) = 243 * (2 * m + 1) + 215 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 449
  rw [data_9_449.1, data_9_449.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_449 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 449) < 512 * (2 * m) + 449 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 449 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_449] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 449) < 512 * (2 * m) + 449 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_449 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 449) < 512 * (2 * m + 1) + 449 := by
  apply refinement_cleared (k := 9) (r := 449) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_449]; decide

end Collatz.Research.RefinementAtlas.Batch249
