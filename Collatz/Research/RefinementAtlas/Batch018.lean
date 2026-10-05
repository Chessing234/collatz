import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 018. -/
namespace Collatz.Research.RefinementAtlas.Batch018
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (5, 24). -/
theorem data_5_24 : oddCount 24 5 = 2 ∧
    acceleratedOrbit 5 24 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_24 : gap 5 24 = 23 ∧ 9 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_24 : threshold 5 24 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_24 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 24) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 24
  rw [data_5_24.1, data_5_24.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_24 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 24) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 24
  rw [data_5_24.1, data_5_24.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_24 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 24) < 32 * (2 * m) + 24 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 24 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_24] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 24) < 32 * (2 * m) + 24 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_24 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 24) < 32 * (2 * m + 1) + 24 := by
  apply refinement_cleared (k := 5) (r := 24) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_24]; decide

/-- Kernel-evaluated parity count and endpoint for (5, 25). -/
theorem data_5_25 : oddCount 25 5 = 3 ∧
    acceleratedOrbit 5 25 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_25 : gap 5 25 = 5 ∧ 27 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_25 : threshold 5 25 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_25 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 25) = 27 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 25
  rw [data_5_25.1, data_5_25.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_25 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 25) = 27 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 25
  rw [data_5_25.1, data_5_25.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_25 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 25) < 32 * (2 * m) + 25 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 25 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_25] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 25) < 32 * (2 * m) + 25 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_25 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 25) < 32 * (2 * m + 1) + 25 := by
  apply refinement_cleared (k := 5) (r := 25) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_25]; decide

/-- Kernel-evaluated parity count and endpoint for (5, 26). -/
theorem data_5_26 : oddCount 26 5 = 2 ∧
    acceleratedOrbit 5 26 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_26 : gap 5 26 = 23 ∧ 9 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_26 : threshold 5 26 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_26 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 26) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 26
  rw [data_5_26.1, data_5_26.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_26 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 26) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 26
  rw [data_5_26.1, data_5_26.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_26 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 26) < 32 * (2 * m) + 26 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 26 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_26] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 26) < 32 * (2 * m) + 26 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_26 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 26) < 32 * (2 * m + 1) + 26 := by
  apply refinement_cleared (k := 5) (r := 26) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_26]; decide

end Collatz.Research.RefinementAtlas.Batch018
