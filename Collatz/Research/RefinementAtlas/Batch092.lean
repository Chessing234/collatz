import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 092. -/
namespace Collatz.Research.RefinementAtlas.Batch092
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 101). -/
theorem data_8_101 : oddCount 101 8 = 3 ∧
    acceleratedOrbit 8 101 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_101 : gap 8 101 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_101 : threshold 8 101 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_101 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 101) = 27 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 101
  rw [data_8_101.1, data_8_101.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_101 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 101) = 27 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 101
  rw [data_8_101.1, data_8_101.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_101 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 101) < 256 * (2 * m) + 101 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 101 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_101] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 101) < 256 * (2 * m) + 101 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_101 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 101) < 256 * (2 * m + 1) + 101 := by
  apply refinement_cleared (k := 8) (r := 101) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_101]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 102). -/
theorem data_8_102 : oddCount 102 8 = 3 ∧
    acceleratedOrbit 8 102 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_102 : gap 8 102 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_102 : threshold 8 102 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_102 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 102) = 27 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 102
  rw [data_8_102.1, data_8_102.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_102 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 102) = 27 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 102
  rw [data_8_102.1, data_8_102.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_102 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 102) < 256 * (2 * m) + 102 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 102 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_102] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 102) < 256 * (2 * m) + 102 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_102 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 102) < 256 * (2 * m + 1) + 102 := by
  apply refinement_cleared (k := 8) (r := 102) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_102]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 104). -/
theorem data_8_104 : oddCount 104 8 = 2 ∧
    acceleratedOrbit 8 104 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_104 : gap 8 104 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_104 : threshold 8 104 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_104 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 104) = 9 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 104
  rw [data_8_104.1, data_8_104.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_104 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 104) = 9 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 104
  rw [data_8_104.1, data_8_104.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_104 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 104) < 256 * (2 * m) + 104 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 104 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_104] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 104) < 256 * (2 * m) + 104 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_104 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 104) < 256 * (2 * m + 1) + 104 := by
  apply refinement_cleared (k := 8) (r := 104) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_104]; decide

end Collatz.Research.RefinementAtlas.Batch092
