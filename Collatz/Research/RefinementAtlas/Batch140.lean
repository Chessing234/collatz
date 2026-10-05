import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 140. -/
namespace Collatz.Research.RefinementAtlas.Batch140
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 16). -/
theorem data_9_16 : oddCount 16 9 = 3 ∧
    acceleratedOrbit 9 16 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_16 : gap 9 16 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_16 : threshold 9 16 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_16 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 16) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 16
  rw [data_9_16.1, data_9_16.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_16 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 16) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 16
  rw [data_9_16.1, data_9_16.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_16 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 16) < 512 * (2 * m) + 16 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 16 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_16] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 16) < 512 * (2 * m) + 16 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_16 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 16) < 512 * (2 * m + 1) + 16 := by
  apply refinement_cleared (k := 9) (r := 16) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_16]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 17). -/
theorem data_9_17 : oddCount 17 9 = 3 ∧
    acceleratedOrbit 9 17 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_17 : gap 9 17 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_17 : threshold 9 17 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_17 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 17) = 27 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 17
  rw [data_9_17.1, data_9_17.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_17 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 17) = 27 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 17
  rw [data_9_17.1, data_9_17.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_17 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 17) < 512 * (2 * m) + 17 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 17 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_17] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 17) < 512 * (2 * m) + 17 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_17 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 17) < 512 * (2 * m + 1) + 17 := by
  apply refinement_cleared (k := 9) (r := 17) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_17]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 18). -/
theorem data_9_18 : oddCount 18 9 = 5 ∧
    acceleratedOrbit 9 18 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_18 : gap 9 18 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_18 : threshold 9 18 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_18 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 18) = 243 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 18
  rw [data_9_18.1, data_9_18.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_18 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 18) = 243 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 18
  rw [data_9_18.1, data_9_18.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_18 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 18) < 512 * (2 * m) + 18 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 18 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_18] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 18) < 512 * (2 * m) + 18 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_18 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 18) < 512 * (2 * m + 1) + 18 := by
  apply refinement_cleared (k := 9) (r := 18) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_18]; decide

end Collatz.Research.RefinementAtlas.Batch140
