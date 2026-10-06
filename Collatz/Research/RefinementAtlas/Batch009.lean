import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 009. -/
namespace Collatz.Research.RefinementAtlas.Batch009
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (4, 3). -/
theorem data_4_3 : oddCount 3 4 = 2 ∧
    acceleratedOrbit 4 3 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_4_3 : gap 4 3 = 7 ∧ 9 < 16 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_4_3 : threshold 4 3 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_4_3 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m) + 3) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 4 (2 * m) 3
  rw [data_4_3.1, data_4_3.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_4_3 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m + 1) + 3) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 4 (2 * m + 1) 3
  rw [data_4_3.1, data_4_3.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_4_3 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m) + 3) < 16 * (2 * m) + 3 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 3 4 < 2 ^ 4 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_4_3] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 4 (16 * (2 * m) + 3) < 16 * (2 * m) + 3 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_4_3 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m + 1) + 3) < 16 * (2 * m + 1) + 3 := by
  apply refinement_cleared (k := 4) (r := 3) (s := 2) (q := 1)
  · decide
  · rw [cutoff_4_3]; decide

/-- Kernel-evaluated parity count and endpoint for (4, 4). -/
theorem data_4_4 : oddCount 4 4 = 1 ∧
    acceleratedOrbit 4 4 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_4_4 : gap 4 4 = 13 ∧ 3 < 16 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_4_4 : threshold 4 4 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_4_4 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m) + 4) = 3 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 4 (2 * m) 4
  rw [data_4_4.1, data_4_4.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_4_4 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m + 1) + 4) = 3 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 4 (2 * m + 1) 4
  rw [data_4_4.1, data_4_4.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_4_4 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m) + 4) < 16 * (2 * m) + 4 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 4 4 < 2 ^ 4 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_4_4] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 4 (16 * (2 * m) + 4) < 16 * (2 * m) + 4 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_4_4 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m + 1) + 4) < 16 * (2 * m + 1) + 4 := by
  apply refinement_cleared (k := 4) (r := 4) (s := 2) (q := 1)
  · decide
  · rw [cutoff_4_4]; decide

/-- Kernel-evaluated parity count and endpoint for (4, 5). -/
theorem data_4_5 : oddCount 5 4 = 1 ∧
    acceleratedOrbit 4 5 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_4_5 : gap 4 5 = 13 ∧ 3 < 16 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_4_5 : threshold 4 5 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_4_5 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m) + 5) = 3 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 4 (2 * m) 5
  rw [data_4_5.1, data_4_5.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_4_5 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m + 1) + 5) = 3 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 4 (2 * m + 1) 5
  rw [data_4_5.1, data_4_5.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_4_5 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m) + 5) < 16 * (2 * m) + 5 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 5 4 < 2 ^ 4 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_4_5] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 4 (16 * (2 * m) + 5) < 16 * (2 * m) + 5 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_4_5 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m + 1) + 5) < 16 * (2 * m + 1) + 5 := by
  apply refinement_cleared (k := 4) (r := 5) (s := 2) (q := 1)
  · decide
  · rw [cutoff_4_5]; decide

end Collatz.Research.RefinementAtlas.Batch009
