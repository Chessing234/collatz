import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 065. -/
namespace Collatz.Research.RefinementAtlas.Batch065
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 3). -/
theorem data_8_3 : oddCount 3 8 = 4 ∧
    acceleratedOrbit 8 3 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_3 : gap 8 3 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_3 : threshold 8 3 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_3 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 3) = 81 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 3
  rw [data_8_3.1, data_8_3.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_3 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 3) = 81 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 3
  rw [data_8_3.1, data_8_3.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_3 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 3) < 256 * (2 * m) + 3 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 3 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_3] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 3) < 256 * (2 * m) + 3 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_3 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 3) < 256 * (2 * m + 1) + 3 := by
  apply refinement_cleared (k := 8) (r := 3) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_3]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 4). -/
theorem data_8_4 : oddCount 4 8 = 3 ∧
    acceleratedOrbit 8 4 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_4 : gap 8 4 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_4 : threshold 8 4 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_4 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 4) = 27 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 4
  rw [data_8_4.1, data_8_4.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_4 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 4) = 27 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 4
  rw [data_8_4.1, data_8_4.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_4 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 4) < 256 * (2 * m) + 4 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 4 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_4] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 4) < 256 * (2 * m) + 4 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_4 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 4) < 256 * (2 * m + 1) + 4 := by
  apply refinement_cleared (k := 8) (r := 4) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_4]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 5). -/
theorem data_8_5 : oddCount 5 8 = 3 ∧
    acceleratedOrbit 8 5 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_5 : gap 8 5 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_5 : threshold 8 5 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_5 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 5) = 27 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 5
  rw [data_8_5.1, data_8_5.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_5 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 5) = 27 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 5
  rw [data_8_5.1, data_8_5.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_5 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 5) < 256 * (2 * m) + 5 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 5 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_5] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 5) < 256 * (2 * m) + 5 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_5 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 5) < 256 * (2 * m + 1) + 5 := by
  apply refinement_cleared (k := 8) (r := 5) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_5]; decide

end Collatz.Research.RefinementAtlas.Batch065
