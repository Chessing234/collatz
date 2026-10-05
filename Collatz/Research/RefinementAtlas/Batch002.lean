import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 002. -/
namespace Collatz.Research.RefinementAtlas.Batch002
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (4, 2). -/
theorem data_4_2 : oddCount 2 4 = 2 ∧
    acceleratedOrbit 4 2 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_4_2 : gap 4 2 = 7 ∧ 9 < 16 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_4_2 : threshold 4 2 = 1 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_4_2 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m) + 2) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 4 (2 * m) 2
  rw [data_4_2.1, data_4_2.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_4_2 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m + 1) + 2) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 4 (2 * m + 1) 2
  rw [data_4_2.1, data_4_2.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_4_2 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m) + 2) < 16 * (2 * m) + 2 ↔ 1 ≤ m := by
  have hc : 3 ^ oddCount 2 4 < 2 ^ 4 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_4_2] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 4 (16 * (2 * m) + 2) < 16 * (2 * m) + 2 ↔ 1 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_4_2 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m + 1) + 2) < 16 * (2 * m + 1) + 2 := by
  apply refinement_cleared (k := 4) (r := 2) (s := 2) (q := 1)
  · decide
  · rw [cutoff_4_2]; decide

/-- Kernel-evaluated parity count and endpoint for (5, 1). -/
theorem data_5_1 : oddCount 1 5 = 3 ∧
    acceleratedOrbit 5 1 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_1 : gap 5 1 = 5 ∧ 27 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_1 : threshold 5 1 = 1 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_1 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 1) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 1
  rw [data_5_1.1, data_5_1.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_1 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 1) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 1
  rw [data_5_1.1, data_5_1.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_1 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 1) < 32 * (2 * m) + 1 ↔ 1 ≤ m := by
  have hc : 3 ^ oddCount 1 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_1] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 1) < 32 * (2 * m) + 1 ↔ 1 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_1 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 1) < 32 * (2 * m + 1) + 1 := by
  apply refinement_cleared (k := 5) (r := 1) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_1]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 1). -/
theorem data_6_1 : oddCount 1 6 = 3 ∧
    acceleratedOrbit 6 1 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_1 : gap 6 1 = 37 ∧ 27 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_1 : threshold 6 1 = 1 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_1 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 1) = 27 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 1
  rw [data_6_1.1, data_6_1.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_1 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 1) = 27 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 1
  rw [data_6_1.1, data_6_1.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_1 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 1) < 64 * (2 * m) + 1 ↔ 1 ≤ m := by
  have hc : 3 ^ oddCount 1 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_1] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 1) < 64 * (2 * m) + 1 ↔ 1 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_1 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 1) < 64 * (2 * m + 1) + 1 := by
  apply refinement_cleared (k := 6) (r := 1) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_1]; decide

end Collatz.Research.RefinementAtlas.Batch002
