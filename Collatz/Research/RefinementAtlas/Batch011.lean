import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 011. -/
namespace Collatz.Research.RefinementAtlas.Batch011
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (4, 12). -/
theorem data_4_12 : oddCount 12 4 = 2 ∧
    acceleratedOrbit 4 12 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_4_12 : gap 4 12 = 7 ∧ 9 < 16 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_4_12 : threshold 4 12 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_4_12 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m) + 12) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 4 (2 * m) 12
  rw [data_4_12.1, data_4_12.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_4_12 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m + 1) + 12) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 4 (2 * m + 1) 12
  rw [data_4_12.1, data_4_12.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_4_12 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m) + 12) < 16 * (2 * m) + 12 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 12 4 < 2 ^ 4 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_4_12] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 4 (16 * (2 * m) + 12) < 16 * (2 * m) + 12 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_4_12 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m + 1) + 12) < 16 * (2 * m + 1) + 12 := by
  apply refinement_cleared (k := 4) (r := 12) (s := 2) (q := 1)
  · decide
  · rw [cutoff_4_12]; decide

/-- Kernel-evaluated parity count and endpoint for (4, 13). -/
theorem data_4_13 : oddCount 13 4 = 2 ∧
    acceleratedOrbit 4 13 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_4_13 : gap 4 13 = 7 ∧ 9 < 16 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_4_13 : threshold 4 13 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_4_13 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m) + 13) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 4 (2 * m) 13
  rw [data_4_13.1, data_4_13.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_4_13 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m + 1) + 13) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 4 (2 * m + 1) 13
  rw [data_4_13.1, data_4_13.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_4_13 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m) + 13) < 16 * (2 * m) + 13 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 13 4 < 2 ^ 4 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_4_13] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 4 (16 * (2 * m) + 13) < 16 * (2 * m) + 13 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_4_13 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m + 1) + 13) < 16 * (2 * m + 1) + 13 := by
  apply refinement_cleared (k := 4) (r := 13) (s := 2) (q := 1)
  · decide
  · rw [cutoff_4_13]; decide

/-- Kernel-evaluated parity count and endpoint for (5, 2). -/
theorem data_5_2 : oddCount 2 5 = 2 ∧
    acceleratedOrbit 5 2 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_2 : gap 5 2 = 23 ∧ 9 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_2 : threshold 5 2 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_2 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 2) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 2
  rw [data_5_2.1, data_5_2.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_2 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 2) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 2
  rw [data_5_2.1, data_5_2.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_2 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 2) < 32 * (2 * m) + 2 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 2 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_2] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 2) < 32 * (2 * m) + 2 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_2 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 2) < 32 * (2 * m + 1) + 2 := by
  apply refinement_cleared (k := 5) (r := 2) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_2]; decide

end Collatz.Research.RefinementAtlas.Batch011
