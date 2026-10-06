import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 001. -/
namespace Collatz.Research.RefinementAtlas.Batch001
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (2, 1). -/
theorem data_2_1 : oddCount 1 2 = 1 ∧
    acceleratedOrbit 2 1 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_2_1 : gap 2 1 = 1 ∧ 3 < 4 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_2_1 : threshold 2 1 = 1 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_2_1 (m : Nat) :
    acceleratedOrbit 2 (4 * (2 * m) + 1) = 3 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 2 (2 * m) 1
  rw [data_2_1.1, data_2_1.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_2_1 (m : Nat) :
    acceleratedOrbit 2 (4 * (2 * m + 1) + 1) = 3 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 2 (2 * m + 1) 1
  rw [data_2_1.1, data_2_1.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_2_1 (m : Nat) :
    acceleratedOrbit 2 (4 * (2 * m) + 1) < 4 * (2 * m) + 1 ↔ 1 ≤ m := by
  have hc : 3 ^ oddCount 1 2 < 2 ^ 2 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_2_1] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 2 (4 * (2 * m) + 1) < 4 * (2 * m) + 1 ↔ 1 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_2_1 (m : Nat) :
    acceleratedOrbit 2 (4 * (2 * m + 1) + 1) < 4 * (2 * m + 1) + 1 := by
  apply refinement_cleared (k := 2) (r := 1) (s := 2) (q := 1)
  · decide
  · rw [cutoff_2_1]; decide

/-- Kernel-evaluated parity count and endpoint for (2, 2). -/
theorem data_2_2 : oddCount 2 2 = 1 ∧
    acceleratedOrbit 2 2 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_2_2 : gap 2 2 = 1 ∧ 3 < 4 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_2_2 : threshold 2 2 = 1 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_2_2 (m : Nat) :
    acceleratedOrbit 2 (4 * (2 * m) + 2) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 2 (2 * m) 2
  rw [data_2_2.1, data_2_2.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_2_2 (m : Nat) :
    acceleratedOrbit 2 (4 * (2 * m + 1) + 2) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 2 (2 * m + 1) 2
  rw [data_2_2.1, data_2_2.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_2_2 (m : Nat) :
    acceleratedOrbit 2 (4 * (2 * m) + 2) < 4 * (2 * m) + 2 ↔ 1 ≤ m := by
  have hc : 3 ^ oddCount 2 2 < 2 ^ 2 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_2_2] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 2 (4 * (2 * m) + 2) < 4 * (2 * m) + 2 ↔ 1 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_2_2 (m : Nat) :
    acceleratedOrbit 2 (4 * (2 * m + 1) + 2) < 4 * (2 * m + 1) + 2 := by
  apply refinement_cleared (k := 2) (r := 2) (s := 2) (q := 1)
  · decide
  · rw [cutoff_2_2]; decide

/-- Kernel-evaluated parity count and endpoint for (4, 1). -/
theorem data_4_1 : oddCount 1 4 = 2 ∧
    acceleratedOrbit 4 1 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_4_1 : gap 4 1 = 7 ∧ 9 < 16 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_4_1 : threshold 4 1 = 1 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_4_1 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m) + 1) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 4 (2 * m) 1
  rw [data_4_1.1, data_4_1.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_4_1 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m + 1) + 1) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 4 (2 * m + 1) 1
  rw [data_4_1.1, data_4_1.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_4_1 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m) + 1) < 16 * (2 * m) + 1 ↔ 1 ≤ m := by
  have hc : 3 ^ oddCount 1 4 < 2 ^ 4 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_4_1] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 4 (16 * (2 * m) + 1) < 16 * (2 * m) + 1 ↔ 1 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_4_1 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m + 1) + 1) < 16 * (2 * m + 1) + 1 := by
  apply refinement_cleared (k := 4) (r := 1) (s := 2) (q := 1)
  · decide
  · rw [cutoff_4_1]; decide

end Collatz.Research.RefinementAtlas.Batch001
