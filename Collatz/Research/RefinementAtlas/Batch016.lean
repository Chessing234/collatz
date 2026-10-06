import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 016. -/
namespace Collatz.Research.RefinementAtlas.Batch016
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (5, 18). -/
theorem data_5_18 : oddCount 18 5 = 3 ∧
    acceleratedOrbit 5 18 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_18 : gap 5 18 = 5 ∧ 27 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_18 : threshold 5 18 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_18 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 18) = 27 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 18
  rw [data_5_18.1, data_5_18.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_18 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 18) = 27 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 18
  rw [data_5_18.1, data_5_18.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_18 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 18) < 32 * (2 * m) + 18 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 18 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_18] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 18) < 32 * (2 * m) + 18 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_18 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 18) < 32 * (2 * m + 1) + 18 := by
  apply refinement_cleared (k := 5) (r := 18) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_18]; decide

/-- Kernel-evaluated parity count and endpoint for (5, 19). -/
theorem data_5_19 : oddCount 19 5 = 3 ∧
    acceleratedOrbit 5 19 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_19 : gap 5 19 = 5 ∧ 27 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_19 : threshold 5 19 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_19 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 19) = 27 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 19
  rw [data_5_19.1, data_5_19.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_19 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 19) = 27 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 19
  rw [data_5_19.1, data_5_19.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_19 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 19) < 32 * (2 * m) + 19 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 19 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_19] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 19) < 32 * (2 * m) + 19 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_19 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 19) < 32 * (2 * m + 1) + 19 := by
  apply refinement_cleared (k := 5) (r := 19) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_19]; decide

/-- Kernel-evaluated parity count and endpoint for (5, 20). -/
theorem data_5_20 : oddCount 20 5 = 1 ∧
    acceleratedOrbit 5 20 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_20 : gap 5 20 = 29 ∧ 3 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_20 : threshold 5 20 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_20 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 20) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 20
  rw [data_5_20.1, data_5_20.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_20 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 20) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 20
  rw [data_5_20.1, data_5_20.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_20 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 20) < 32 * (2 * m) + 20 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 20 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_20] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 20) < 32 * (2 * m) + 20 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_20 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 20) < 32 * (2 * m + 1) + 20 := by
  apply refinement_cleared (k := 5) (r := 20) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_20]; decide

end Collatz.Research.RefinementAtlas.Batch016
