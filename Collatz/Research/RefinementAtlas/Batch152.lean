import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 152. -/
namespace Collatz.Research.RefinementAtlas.Batch152
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 58). -/
theorem data_9_58 : oddCount 58 9 = 4 ∧
    acceleratedOrbit 9 58 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_58 : gap 9 58 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_58 : threshold 9 58 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_58 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 58) = 81 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 58
  rw [data_9_58.1, data_9_58.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_58 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 58) = 81 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 58
  rw [data_9_58.1, data_9_58.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_58 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 58) < 512 * (2 * m) + 58 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 58 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_58] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 58) < 512 * (2 * m) + 58 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_58 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 58) < 512 * (2 * m + 1) + 58 := by
  apply refinement_cleared (k := 9) (r := 58) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_58]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 59). -/
theorem data_9_59 : oddCount 59 9 = 5 ∧
    acceleratedOrbit 9 59 = 29 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_59 : gap 9 59 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_59 : threshold 9 59 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_59 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 59) = 243 * (2 * m) + 29 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 59
  rw [data_9_59.1, data_9_59.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_59 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 59) = 243 * (2 * m + 1) + 29 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 59
  rw [data_9_59.1, data_9_59.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_59 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 59) < 512 * (2 * m) + 59 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 59 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_59] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 59) < 512 * (2 * m) + 59 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_59 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 59) < 512 * (2 * m + 1) + 59 := by
  apply refinement_cleared (k := 9) (r := 59) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_59]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 60). -/
theorem data_9_60 : oddCount 60 9 = 4 ∧
    acceleratedOrbit 9 60 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_60 : gap 9 60 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_60 : threshold 9 60 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_60 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 60) = 81 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 60
  rw [data_9_60.1, data_9_60.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_60 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 60) = 81 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 60
  rw [data_9_60.1, data_9_60.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_60 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 60) < 512 * (2 * m) + 60 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 60 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_60] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 60) < 512 * (2 * m) + 60 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_60 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 60) < 512 * (2 * m + 1) + 60 := by
  apply refinement_cleared (k := 9) (r := 60) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_60]; decide

end Collatz.Research.RefinementAtlas.Batch152
