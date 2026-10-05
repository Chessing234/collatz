import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 290. -/
namespace Collatz.Research.RefinementAtlas.Batch290
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 102). -/
theorem data_10_102 : oddCount 102 10 = 5 ∧
    acceleratedOrbit 10 102 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_102 : gap 10 102 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_102 : threshold 10 102 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_102 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 102) = 243 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 102
  rw [data_10_102.1, data_10_102.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_102 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 102) = 243 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 102
  rw [data_10_102.1, data_10_102.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_102 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 102) < 1024 * (2 * m) + 102 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 102 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_102] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 102) < 1024 * (2 * m) + 102 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_102 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 102) < 1024 * (2 * m + 1) + 102 := by
  apply refinement_cleared (k := 10) (r := 102) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_102]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 104). -/
theorem data_10_104 : oddCount 104 10 = 2 ∧
    acceleratedOrbit 10 104 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_104 : gap 10 104 = 1015 ∧ 9 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_104 : threshold 10 104 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_104 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 104) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 104
  rw [data_10_104.1, data_10_104.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_104 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 104) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 104
  rw [data_10_104.1, data_10_104.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_104 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 104) < 1024 * (2 * m) + 104 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 104 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_104] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 104) < 1024 * (2 * m) + 104 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_104 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 104) < 1024 * (2 * m + 1) + 104 := by
  apply refinement_cleared (k := 10) (r := 104) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_104]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 105). -/
theorem data_10_105 : oddCount 105 10 = 6 ∧
    acceleratedOrbit 10 105 = 76 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_105 : gap 10 105 = 295 ∧ 729 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_105 : threshold 10 105 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_105 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 105) = 729 * (2 * m) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 105
  rw [data_10_105.1, data_10_105.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_105 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 105) = 729 * (2 * m + 1) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 105
  rw [data_10_105.1, data_10_105.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_105 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 105) < 1024 * (2 * m) + 105 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 105 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_105] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 105) < 1024 * (2 * m) + 105 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_105 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 105) < 1024 * (2 * m + 1) + 105 := by
  apply refinement_cleared (k := 10) (r := 105) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_105]; decide

end Collatz.Research.RefinementAtlas.Batch290
