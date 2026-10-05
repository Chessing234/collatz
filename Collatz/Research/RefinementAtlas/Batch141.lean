import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 141. -/
namespace Collatz.Research.RefinementAtlas.Batch141
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 19). -/
theorem data_9_19 : oddCount 19 9 = 5 ∧
    acceleratedOrbit 9 19 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_19 : gap 9 19 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_19 : threshold 9 19 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_19 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 19) = 243 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 19
  rw [data_9_19.1, data_9_19.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_19 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 19) = 243 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 19
  rw [data_9_19.1, data_9_19.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_19 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 19) < 512 * (2 * m) + 19 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 19 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_19] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 19) < 512 * (2 * m) + 19 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_19 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 19) < 512 * (2 * m + 1) + 19 := by
  apply refinement_cleared (k := 9) (r := 19) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_19]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 20). -/
theorem data_9_20 : oddCount 20 9 = 3 ∧
    acceleratedOrbit 9 20 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_20 : gap 9 20 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_20 : threshold 9 20 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_20 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 20) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 20
  rw [data_9_20.1, data_9_20.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_20 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 20) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 20
  rw [data_9_20.1, data_9_20.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_20 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 20) < 512 * (2 * m) + 20 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 20 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_20] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 20) < 512 * (2 * m) + 20 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_20 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 20) < 512 * (2 * m + 1) + 20 := by
  apply refinement_cleared (k := 9) (r := 20) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_20]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 21). -/
theorem data_9_21 : oddCount 21 9 = 3 ∧
    acceleratedOrbit 9 21 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_21 : gap 9 21 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_21 : threshold 9 21 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_21 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 21) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 21
  rw [data_9_21.1, data_9_21.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_21 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 21) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 21
  rw [data_9_21.1, data_9_21.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_21 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 21) < 512 * (2 * m) + 21 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 21 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_21] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 21) < 512 * (2 * m) + 21 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_21 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 21) < 512 * (2 * m + 1) + 21 := by
  apply refinement_cleared (k := 9) (r := 21) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_21]; decide

end Collatz.Research.RefinementAtlas.Batch141
