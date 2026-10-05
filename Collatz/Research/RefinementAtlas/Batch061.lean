import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 061. -/
namespace Collatz.Research.RefinementAtlas.Batch061
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 109). -/
theorem data_7_109 : oddCount 109 7 = 4 ∧
    acceleratedOrbit 7 109 = 71 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_109 : gap 7 109 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_109 : threshold 7 109 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_109 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 109) = 81 * (2 * m) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 109
  rw [data_7_109.1, data_7_109.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_109 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 109) = 81 * (2 * m + 1) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 109
  rw [data_7_109.1, data_7_109.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_109 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 109) < 128 * (2 * m) + 109 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 109 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_109] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 109) < 128 * (2 * m) + 109 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_109 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 109) < 128 * (2 * m + 1) + 109 := by
  apply refinement_cleared (k := 7) (r := 109) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_109]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 110). -/
theorem data_7_110 : oddCount 110 7 = 4 ∧
    acceleratedOrbit 7 110 = 71 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_110 : gap 7 110 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_110 : threshold 7 110 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_110 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 110) = 81 * (2 * m) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 110
  rw [data_7_110.1, data_7_110.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_110 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 110) = 81 * (2 * m + 1) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 110
  rw [data_7_110.1, data_7_110.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_110 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 110) < 128 * (2 * m) + 110 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 110 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_110] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 110) < 128 * (2 * m) + 110 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_110 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 110) < 128 * (2 * m + 1) + 110 := by
  apply refinement_cleared (k := 7) (r := 110) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_110]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 112). -/
theorem data_7_112 : oddCount 112 7 = 3 ∧
    acceleratedOrbit 7 112 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_112 : gap 7 112 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_112 : threshold 7 112 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_112 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 112) = 27 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 112
  rw [data_7_112.1, data_7_112.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_112 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 112) = 27 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 112
  rw [data_7_112.1, data_7_112.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_112 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 112) < 128 * (2 * m) + 112 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 112 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_112] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 112) < 128 * (2 * m) + 112 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_112 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 112) < 128 * (2 * m + 1) + 112 := by
  apply refinement_cleared (k := 7) (r := 112) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_112]; decide

end Collatz.Research.RefinementAtlas.Batch061
