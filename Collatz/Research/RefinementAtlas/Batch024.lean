import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 024. -/
namespace Collatz.Research.RefinementAtlas.Batch024
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (6, 22). -/
theorem data_6_22 : oddCount 22 6 = 3 ∧
    acceleratedOrbit 6 22 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_22 : gap 6 22 = 37 ∧ 27 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_22 : threshold 6 22 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_22 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 22) = 27 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 22
  rw [data_6_22.1, data_6_22.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_22 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 22) = 27 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 22
  rw [data_6_22.1, data_6_22.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_22 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 22) < 64 * (2 * m) + 22 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 22 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_22] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 22) < 64 * (2 * m) + 22 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_22 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 22) < 64 * (2 * m + 1) + 22 := by
  apply refinement_cleared (k := 6) (r := 22) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_22]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 23). -/
theorem data_6_23 : oddCount 23 6 = 3 ∧
    acceleratedOrbit 6 23 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_23 : gap 6 23 = 37 ∧ 27 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_23 : threshold 6 23 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_23 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 23) = 27 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 23
  rw [data_6_23.1, data_6_23.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_23 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 23) = 27 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 23
  rw [data_6_23.1, data_6_23.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_23 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 23) < 64 * (2 * m) + 23 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 23 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_23] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 23) < 64 * (2 * m) + 23 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_23 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 23) < 64 * (2 * m + 1) + 23 := by
  apply refinement_cleared (k := 6) (r := 23) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_23]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 24). -/
theorem data_6_24 : oddCount 24 6 = 2 ∧
    acceleratedOrbit 6 24 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_24 : gap 6 24 = 55 ∧ 9 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_24 : threshold 6 24 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_24 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 24) = 9 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 24
  rw [data_6_24.1, data_6_24.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_24 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 24) = 9 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 24
  rw [data_6_24.1, data_6_24.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_24 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 24) < 64 * (2 * m) + 24 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 24 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_24] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 24) < 64 * (2 * m) + 24 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_24 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 24) < 64 * (2 * m + 1) + 24 := by
  apply refinement_cleared (k := 6) (r := 24) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_24]; decide

end Collatz.Research.RefinementAtlas.Batch024
