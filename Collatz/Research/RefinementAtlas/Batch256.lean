import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 256. -/
namespace Collatz.Research.RefinementAtlas.Batch256
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 477). -/
theorem data_9_477 : oddCount 477 9 = 4 ∧
    acceleratedOrbit 9 477 = 76 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_477 : gap 9 477 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_477 : threshold 9 477 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_477 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 477) = 81 * (2 * m) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 477
  rw [data_9_477.1, data_9_477.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_477 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 477) = 81 * (2 * m + 1) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 477
  rw [data_9_477.1, data_9_477.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_477 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 477) < 512 * (2 * m) + 477 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 477 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_477] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 477) < 512 * (2 * m) + 477 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_477 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 477) < 512 * (2 * m + 1) + 477 := by
  apply refinement_cleared (k := 9) (r := 477) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_477]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 480). -/
theorem data_9_480 : oddCount 480 9 = 4 ∧
    acceleratedOrbit 9 480 = 80 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_480 : gap 9 480 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_480 : threshold 9 480 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_480 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 480) = 81 * (2 * m) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 480
  rw [data_9_480.1, data_9_480.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_480 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 480) = 81 * (2 * m + 1) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 480
  rw [data_9_480.1, data_9_480.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_480 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 480) < 512 * (2 * m) + 480 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 480 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_480] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 480) < 512 * (2 * m) + 480 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_480 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 480) < 512 * (2 * m + 1) + 480 := by
  apply refinement_cleared (k := 9) (r := 480) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_480]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 482). -/
theorem data_9_482 : oddCount 482 9 = 3 ∧
    acceleratedOrbit 9 482 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_482 : gap 9 482 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_482 : threshold 9 482 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_482 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 482) = 27 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 482
  rw [data_9_482.1, data_9_482.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_482 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 482) = 27 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 482
  rw [data_9_482.1, data_9_482.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_482 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 482) < 512 * (2 * m) + 482 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 482 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_482] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 482) < 512 * (2 * m) + 482 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_482 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 482) < 512 * (2 * m + 1) + 482 := by
  apply refinement_cleared (k := 9) (r := 482) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_482]; decide

end Collatz.Research.RefinementAtlas.Batch256
