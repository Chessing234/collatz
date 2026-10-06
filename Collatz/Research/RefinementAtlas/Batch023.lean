import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 023. -/
namespace Collatz.Research.RefinementAtlas.Batch023
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (6, 17). -/
theorem data_6_17 : oddCount 17 6 = 3 ∧
    acceleratedOrbit 6 17 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_17 : gap 6 17 = 37 ∧ 27 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_17 : threshold 6 17 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_17 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 17) = 27 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 17
  rw [data_6_17.1, data_6_17.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_17 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 17) = 27 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 17
  rw [data_6_17.1, data_6_17.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_17 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 17) < 64 * (2 * m) + 17 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 17 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_17] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 17) < 64 * (2 * m) + 17 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_17 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 17) < 64 * (2 * m + 1) + 17 := by
  apply refinement_cleared (k := 6) (r := 17) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_17]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 20). -/
theorem data_6_20 : oddCount 20 6 = 1 ∧
    acceleratedOrbit 6 20 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_20 : gap 6 20 = 61 ∧ 3 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_20 : threshold 6 20 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_20 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 20) = 3 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 20
  rw [data_6_20.1, data_6_20.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_20 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 20) = 3 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 20
  rw [data_6_20.1, data_6_20.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_20 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 20) < 64 * (2 * m) + 20 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 20 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_20] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 20) < 64 * (2 * m) + 20 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_20 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 20) < 64 * (2 * m + 1) + 20 := by
  apply refinement_cleared (k := 6) (r := 20) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_20]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 21). -/
theorem data_6_21 : oddCount 21 6 = 1 ∧
    acceleratedOrbit 6 21 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_21 : gap 6 21 = 61 ∧ 3 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_21 : threshold 6 21 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_21 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 21) = 3 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 21
  rw [data_6_21.1, data_6_21.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_21 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 21) = 3 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 21
  rw [data_6_21.1, data_6_21.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_21 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 21) < 64 * (2 * m) + 21 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 21 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_21] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 21) < 64 * (2 * m) + 21 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_21 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 21) < 64 * (2 * m + 1) + 21 := by
  apply refinement_cleared (k := 6) (r := 21) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_21]; decide

end Collatz.Research.RefinementAtlas.Batch023
