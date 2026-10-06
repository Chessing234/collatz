import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 042. -/
namespace Collatz.Research.RefinementAtlas.Batch042
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 33). -/
theorem data_7_33 : oddCount 33 7 = 4 ∧
    acceleratedOrbit 7 33 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_33 : gap 7 33 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_33 : threshold 7 33 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_33 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 33) = 81 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 33
  rw [data_7_33.1, data_7_33.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_33 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 33) = 81 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 33
  rw [data_7_33.1, data_7_33.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_33 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 33) < 128 * (2 * m) + 33 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 33 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_33] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 33) < 128 * (2 * m) + 33 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_33 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 33) < 128 * (2 * m + 1) + 33 := by
  apply refinement_cleared (k := 7) (r := 33) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_33]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 34). -/
theorem data_7_34 : oddCount 34 7 = 3 ∧
    acceleratedOrbit 7 34 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_34 : gap 7 34 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_34 : threshold 7 34 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_34 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 34) = 27 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 34
  rw [data_7_34.1, data_7_34.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_34 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 34) = 27 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 34
  rw [data_7_34.1, data_7_34.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_34 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 34) < 128 * (2 * m) + 34 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 34 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_34] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 34) < 128 * (2 * m) + 34 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_34 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 34) < 128 * (2 * m + 1) + 34 := by
  apply refinement_cleared (k := 7) (r := 34) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_34]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 35). -/
theorem data_7_35 : oddCount 35 7 = 3 ∧
    acceleratedOrbit 7 35 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_35 : gap 7 35 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_35 : threshold 7 35 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_35 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 35) = 27 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 35
  rw [data_7_35.1, data_7_35.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_35 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 35) = 27 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 35
  rw [data_7_35.1, data_7_35.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_35 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 35) < 128 * (2 * m) + 35 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 35 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_35] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 35) < 128 * (2 * m) + 35 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_35 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 35) < 128 * (2 * m + 1) + 35 := by
  apply refinement_cleared (k := 7) (r := 35) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_35]; decide

end Collatz.Research.RefinementAtlas.Batch042
