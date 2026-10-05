import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 037. -/
namespace Collatz.Research.RefinementAtlas.Batch037
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 16). -/
theorem data_7_16 : oddCount 16 7 = 2 ∧
    acceleratedOrbit 7 16 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_16 : gap 7 16 = 119 ∧ 9 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_16 : threshold 7 16 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_16 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 16) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 16
  rw [data_7_16.1, data_7_16.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_16 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 16) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 16
  rw [data_7_16.1, data_7_16.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_16 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 16) < 128 * (2 * m) + 16 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 16 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_16] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 16) < 128 * (2 * m) + 16 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_16 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 16) < 128 * (2 * m + 1) + 16 := by
  apply refinement_cleared (k := 7) (r := 16) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_16]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 17). -/
theorem data_7_17 : oddCount 17 7 = 3 ∧
    acceleratedOrbit 7 17 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_17 : gap 7 17 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_17 : threshold 7 17 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_17 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 17) = 27 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 17
  rw [data_7_17.1, data_7_17.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_17 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 17) = 27 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 17
  rw [data_7_17.1, data_7_17.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_17 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 17) < 128 * (2 * m) + 17 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 17 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_17] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 17) < 128 * (2 * m) + 17 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_17 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 17) < 128 * (2 * m + 1) + 17 := by
  apply refinement_cleared (k := 7) (r := 17) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_17]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 18). -/
theorem data_7_18 : oddCount 18 7 = 4 ∧
    acceleratedOrbit 7 18 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_18 : gap 7 18 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_18 : threshold 7 18 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_18 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 18) = 81 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 18
  rw [data_7_18.1, data_7_18.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_18 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 18) = 81 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 18
  rw [data_7_18.1, data_7_18.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_18 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 18) < 128 * (2 * m) + 18 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 18 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_18] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 18) < 128 * (2 * m) + 18 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_18 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 18) < 128 * (2 * m + 1) + 18 := by
  apply refinement_cleared (k := 7) (r := 18) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_18]; decide

end Collatz.Research.RefinementAtlas.Batch037
