import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 049. -/
namespace Collatz.Research.RefinementAtlas.Batch049
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 59). -/
theorem data_7_59 : oddCount 59 7 = 4 ∧
    acceleratedOrbit 7 59 = 38 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_59 : gap 7 59 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_59 : threshold 7 59 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_59 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 59) = 81 * (2 * m) + 38 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 59
  rw [data_7_59.1, data_7_59.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_59 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 59) = 81 * (2 * m + 1) + 38 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 59
  rw [data_7_59.1, data_7_59.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_59 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 59) < 128 * (2 * m) + 59 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 59 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_59] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 59) < 128 * (2 * m) + 59 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_59 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 59) < 128 * (2 * m + 1) + 59 := by
  apply refinement_cleared (k := 7) (r := 59) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_59]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 60). -/
theorem data_7_60 : oddCount 60 7 = 4 ∧
    acceleratedOrbit 7 60 = 40 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_60 : gap 7 60 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_60 : threshold 7 60 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_60 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 60) = 81 * (2 * m) + 40 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 60
  rw [data_7_60.1, data_7_60.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_60 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 60) = 81 * (2 * m + 1) + 40 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 60
  rw [data_7_60.1, data_7_60.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_60 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 60) < 128 * (2 * m) + 60 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 60 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_60] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 60) < 128 * (2 * m) + 60 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_60 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 60) < 128 * (2 * m + 1) + 60 := by
  apply refinement_cleared (k := 7) (r := 60) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_60]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 61). -/
theorem data_7_61 : oddCount 61 7 = 4 ∧
    acceleratedOrbit 7 61 = 40 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_61 : gap 7 61 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_61 : threshold 7 61 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_61 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 61) = 81 * (2 * m) + 40 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 61
  rw [data_7_61.1, data_7_61.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_61 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 61) = 81 * (2 * m + 1) + 40 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 61
  rw [data_7_61.1, data_7_61.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_61 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 61) < 128 * (2 * m) + 61 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 61 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_61] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 61) < 128 * (2 * m) + 61 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_61 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 61) < 128 * (2 * m + 1) + 61 := by
  apply refinement_cleared (k := 7) (r := 61) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_61]; decide

end Collatz.Research.RefinementAtlas.Batch049
