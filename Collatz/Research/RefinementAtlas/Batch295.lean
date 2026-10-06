import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 295. -/
namespace Collatz.Research.RefinementAtlas.Batch295
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 124). -/
theorem data_10_124 : oddCount 124 10 = 6 ∧
    acceleratedOrbit 10 124 = 91 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_124 : gap 10 124 = 295 ∧ 729 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_124 : threshold 10 124 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_124 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 124) = 729 * (2 * m) + 91 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 124
  rw [data_10_124.1, data_10_124.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_124 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 124) = 729 * (2 * m + 1) + 91 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 124
  rw [data_10_124.1, data_10_124.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_124 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 124) < 1024 * (2 * m) + 124 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 124 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_124] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 124) < 1024 * (2 * m) + 124 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_124 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 124) < 1024 * (2 * m + 1) + 124 := by
  apply refinement_cleared (k := 10) (r := 124) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_124]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 125). -/
theorem data_10_125 : oddCount 125 10 = 6 ∧
    acceleratedOrbit 10 125 = 91 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_125 : gap 10 125 = 295 ∧ 729 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_125 : threshold 10 125 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_125 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 125) = 729 * (2 * m) + 91 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 125
  rw [data_10_125.1, data_10_125.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_125 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 125) = 729 * (2 * m + 1) + 91 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 125
  rw [data_10_125.1, data_10_125.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_125 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 125) < 1024 * (2 * m) + 125 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 125 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_125] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 125) < 1024 * (2 * m) + 125 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_125 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 125) < 1024 * (2 * m + 1) + 125 := by
  apply refinement_cleared (k := 10) (r := 125) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_125]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 126). -/
theorem data_10_126 : oddCount 126 10 = 6 ∧
    acceleratedOrbit 10 126 = 91 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_126 : gap 10 126 = 295 ∧ 729 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_126 : threshold 10 126 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_126 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 126) = 729 * (2 * m) + 91 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 126
  rw [data_10_126.1, data_10_126.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_126 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 126) = 729 * (2 * m + 1) + 91 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 126
  rw [data_10_126.1, data_10_126.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_126 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 126) < 1024 * (2 * m) + 126 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 126 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_126] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 126) < 1024 * (2 * m) + 126 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_126 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 126) < 1024 * (2 * m + 1) + 126 := by
  apply refinement_cleared (k := 10) (r := 126) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_126]; decide

end Collatz.Research.RefinementAtlas.Batch295
