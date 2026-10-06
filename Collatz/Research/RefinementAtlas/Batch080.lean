import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 080. -/
namespace Collatz.Research.RefinementAtlas.Batch080
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 59). -/
theorem data_8_59 : oddCount 59 8 = 4 ∧
    acceleratedOrbit 8 59 = 19 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_59 : gap 8 59 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_59 : threshold 8 59 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_59 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 59) = 81 * (2 * m) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 59
  rw [data_8_59.1, data_8_59.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_59 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 59) = 81 * (2 * m + 1) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 59
  rw [data_8_59.1, data_8_59.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_59 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 59) < 256 * (2 * m) + 59 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 59 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_59] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 59) < 256 * (2 * m) + 59 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_59 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 59) < 256 * (2 * m + 1) + 59 := by
  apply refinement_cleared (k := 8) (r := 59) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_59]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 60). -/
theorem data_8_60 : oddCount 60 8 = 4 ∧
    acceleratedOrbit 8 60 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_60 : gap 8 60 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_60 : threshold 8 60 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_60 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 60) = 81 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 60
  rw [data_8_60.1, data_8_60.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_60 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 60) = 81 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 60
  rw [data_8_60.1, data_8_60.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_60 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 60) < 256 * (2 * m) + 60 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 60 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_60] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 60) < 256 * (2 * m) + 60 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_60 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 60) < 256 * (2 * m + 1) + 60 := by
  apply refinement_cleared (k := 8) (r := 60) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_60]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 61). -/
theorem data_8_61 : oddCount 61 8 = 4 ∧
    acceleratedOrbit 8 61 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_61 : gap 8 61 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_61 : threshold 8 61 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_61 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 61) = 81 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 61
  rw [data_8_61.1, data_8_61.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_61 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 61) = 81 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 61
  rw [data_8_61.1, data_8_61.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_61 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 61) < 256 * (2 * m) + 61 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 61 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_61] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 61) < 256 * (2 * m) + 61 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_61 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 61) < 256 * (2 * m + 1) + 61 := by
  apply refinement_cleared (k := 8) (r := 61) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_61]; decide

end Collatz.Research.RefinementAtlas.Batch080
