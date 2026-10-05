import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 278. -/
namespace Collatz.Research.RefinementAtlas.Batch278
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 57). -/
theorem data_10_57 : oddCount 57 10 = 5 ∧
    acceleratedOrbit 10 57 = 14 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_57 : gap 10 57 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_57 : threshold 10 57 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_57 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 57) = 243 * (2 * m) + 14 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 57
  rw [data_10_57.1, data_10_57.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_57 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 57) = 243 * (2 * m + 1) + 14 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 57
  rw [data_10_57.1, data_10_57.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_57 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 57) < 1024 * (2 * m) + 57 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 57 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_57] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 57) < 1024 * (2 * m) + 57 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_57 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 57) < 1024 * (2 * m + 1) + 57 := by
  apply refinement_cleared (k := 10) (r := 57) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_57]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 58). -/
theorem data_10_58 : oddCount 58 10 = 4 ∧
    acceleratedOrbit 10 58 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_58 : gap 10 58 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_58 : threshold 10 58 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_58 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 58) = 81 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 58
  rw [data_10_58.1, data_10_58.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_58 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 58) = 81 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 58
  rw [data_10_58.1, data_10_58.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_58 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 58) < 1024 * (2 * m) + 58 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 58 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_58] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 58) < 1024 * (2 * m) + 58 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_58 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 58) < 1024 * (2 * m + 1) + 58 := by
  apply refinement_cleared (k := 10) (r := 58) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_58]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 59). -/
theorem data_10_59 : oddCount 59 10 = 6 ∧
    acceleratedOrbit 10 59 = 44 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_59 : gap 10 59 = 295 ∧ 729 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_59 : threshold 10 59 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_59 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 59) = 729 * (2 * m) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 59
  rw [data_10_59.1, data_10_59.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_59 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 59) = 729 * (2 * m + 1) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 59
  rw [data_10_59.1, data_10_59.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_59 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 59) < 1024 * (2 * m) + 59 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 59 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_59] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 59) < 1024 * (2 * m) + 59 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_59 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 59) < 1024 * (2 * m + 1) + 59 := by
  apply refinement_cleared (k := 10) (r := 59) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_59]; decide

end Collatz.Research.RefinementAtlas.Batch278
