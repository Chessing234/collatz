import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 003. -/
namespace Collatz.Research.RefinementAtlas.Batch003
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (6, 2). -/
theorem data_6_2 : oddCount 2 6 = 3 ∧
    acceleratedOrbit 6 2 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_2 : gap 6 2 = 37 ∧ 27 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_2 : threshold 6 2 = 1 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_2 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 2) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 2
  rw [data_6_2.1, data_6_2.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_2 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 2) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 2
  rw [data_6_2.1, data_6_2.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_2 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 2) < 64 * (2 * m) + 2 ↔ 1 ≤ m := by
  have hc : 3 ^ oddCount 2 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_2] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 2) < 64 * (2 * m) + 2 ↔ 1 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_2 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 2) < 64 * (2 * m + 1) + 2 := by
  apply refinement_cleared (k := 6) (r := 2) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_2]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 1). -/
theorem data_7_1 : oddCount 1 7 = 4 ∧
    acceleratedOrbit 7 1 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_1 : gap 7 1 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_1 : threshold 7 1 = 1 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_1 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 1) = 81 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 1
  rw [data_7_1.1, data_7_1.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_1 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 1) = 81 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 1
  rw [data_7_1.1, data_7_1.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_1 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 1) < 128 * (2 * m) + 1 ↔ 1 ≤ m := by
  have hc : 3 ^ oddCount 1 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_1] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 1) < 128 * (2 * m) + 1 ↔ 1 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_1 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 1) < 128 * (2 * m + 1) + 1 := by
  apply refinement_cleared (k := 7) (r := 1) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_1]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 1). -/
theorem data_8_1 : oddCount 1 8 = 4 ∧
    acceleratedOrbit 8 1 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_1 : gap 8 1 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_1 : threshold 8 1 = 1 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_1 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 1) = 81 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 1
  rw [data_8_1.1, data_8_1.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_1 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 1) = 81 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 1
  rw [data_8_1.1, data_8_1.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_1 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 1) < 256 * (2 * m) + 1 ↔ 1 ≤ m := by
  have hc : 3 ^ oddCount 1 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_1] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 1) < 256 * (2 * m) + 1 ↔ 1 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_1 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 1) < 256 * (2 * m + 1) + 1 := by
  apply refinement_cleared (k := 8) (r := 1) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_1]; decide

end Collatz.Research.RefinementAtlas.Batch003
