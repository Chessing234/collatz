import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 025. -/
namespace Collatz.Research.RefinementAtlas.Batch025
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (6, 25). -/
theorem data_6_25 : oddCount 25 6 = 3 ∧
    acceleratedOrbit 6 25 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_25 : gap 6 25 = 37 ∧ 27 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_25 : threshold 6 25 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_25 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 25) = 27 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 25
  rw [data_6_25.1, data_6_25.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_25 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 25) = 27 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 25
  rw [data_6_25.1, data_6_25.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_25 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 25) < 64 * (2 * m) + 25 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 25 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_25] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 25) < 64 * (2 * m) + 25 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_25 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 25) < 64 * (2 * m + 1) + 25 := by
  apply refinement_cleared (k := 6) (r := 25) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_25]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 26). -/
theorem data_6_26 : oddCount 26 6 = 2 ∧
    acceleratedOrbit 6 26 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_26 : gap 6 26 = 55 ∧ 9 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_26 : threshold 6 26 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_26 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 26) = 9 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 26
  rw [data_6_26.1, data_6_26.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_26 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 26) = 9 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 26
  rw [data_6_26.1, data_6_26.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_26 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 26) < 64 * (2 * m) + 26 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 26 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_26] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 26) < 64 * (2 * m) + 26 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_26 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 26) < 64 * (2 * m + 1) + 26 := by
  apply refinement_cleared (k := 6) (r := 26) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_26]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 28). -/
theorem data_6_28 : oddCount 28 6 = 3 ∧
    acceleratedOrbit 6 28 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_28 : gap 6 28 = 37 ∧ 27 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_28 : threshold 6 28 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_28 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 28) = 27 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 28
  rw [data_6_28.1, data_6_28.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_28 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 28) = 27 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 28
  rw [data_6_28.1, data_6_28.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_28 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 28) < 64 * (2 * m) + 28 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 28 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_28] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 28) < 64 * (2 * m) + 28 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_28 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 28) < 64 * (2 * m + 1) + 28 := by
  apply refinement_cleared (k := 6) (r := 28) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_28]; decide

end Collatz.Research.RefinementAtlas.Batch025
