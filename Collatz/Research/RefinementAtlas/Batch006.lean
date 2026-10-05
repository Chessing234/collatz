import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 006. -/
namespace Collatz.Research.RefinementAtlas.Batch006
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 1). -/
theorem data_9_1 : oddCount 1 9 = 5 ∧
    acceleratedOrbit 9 1 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_1 : gap 9 1 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_1 : threshold 9 1 = 1 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_1 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 1) = 243 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 1
  rw [data_9_1.1, data_9_1.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_1 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 1) = 243 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 1
  rw [data_9_1.1, data_9_1.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_1 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 1) < 512 * (2 * m) + 1 ↔ 1 ≤ m := by
  have hc : 3 ^ oddCount 1 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_1] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 1) < 512 * (2 * m) + 1 ↔ 1 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_1 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 1) < 512 * (2 * m + 1) + 1 := by
  apply refinement_cleared (k := 9) (r := 1) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_1]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 1). -/
theorem data_10_1 : oddCount 1 10 = 5 ∧
    acceleratedOrbit 10 1 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_1 : gap 10 1 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_1 : threshold 10 1 = 1 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_1 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 1) = 243 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 1
  rw [data_10_1.1, data_10_1.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_1 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 1) = 243 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 1
  rw [data_10_1.1, data_10_1.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_1 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 1) < 1024 * (2 * m) + 1 ↔ 1 ≤ m := by
  have hc : 3 ^ oddCount 1 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_1] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 1) < 1024 * (2 * m) + 1 ↔ 1 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_1 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 1) < 1024 * (2 * m + 1) + 1 := by
  apply refinement_cleared (k := 10) (r := 1) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_1]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 2). -/
theorem data_10_2 : oddCount 2 10 = 5 ∧
    acceleratedOrbit 10 2 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_2 : gap 10 2 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_2 : threshold 10 2 = 1 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_2 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 2) = 243 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 2
  rw [data_10_2.1, data_10_2.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_2 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 2) = 243 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 2
  rw [data_10_2.1, data_10_2.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_2 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 2) < 1024 * (2 * m) + 2 ↔ 1 ≤ m := by
  have hc : 3 ^ oddCount 2 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_2] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 2) < 1024 * (2 * m) + 2 ↔ 1 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_2 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 2) < 1024 * (2 * m + 1) + 2 := by
  apply refinement_cleared (k := 10) (r := 2) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_2]; decide

end Collatz.Research.RefinementAtlas.Batch006
