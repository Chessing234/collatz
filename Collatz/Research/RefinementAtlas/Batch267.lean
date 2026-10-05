import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 267. -/
namespace Collatz.Research.RefinementAtlas.Batch267
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 18). -/
theorem data_10_18 : oddCount 18 10 = 5 ∧
    acceleratedOrbit 10 18 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_18 : gap 10 18 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_18 : threshold 10 18 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_18 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 18) = 243 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 18
  rw [data_10_18.1, data_10_18.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_18 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 18) = 243 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 18
  rw [data_10_18.1, data_10_18.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_18 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 18) < 1024 * (2 * m) + 18 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 18 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_18] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 18) < 1024 * (2 * m) + 18 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_18 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 18) < 1024 * (2 * m + 1) + 18 := by
  apply refinement_cleared (k := 10) (r := 18) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_18]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 19). -/
theorem data_10_19 : oddCount 19 10 = 5 ∧
    acceleratedOrbit 10 19 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_19 : gap 10 19 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_19 : threshold 10 19 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_19 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 19) = 243 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 19
  rw [data_10_19.1, data_10_19.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_19 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 19) = 243 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 19
  rw [data_10_19.1, data_10_19.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_19 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 19) < 1024 * (2 * m) + 19 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 19 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_19] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 19) < 1024 * (2 * m) + 19 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_19 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 19) < 1024 * (2 * m + 1) + 19 := by
  apply refinement_cleared (k := 10) (r := 19) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_19]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 20). -/
theorem data_10_20 : oddCount 20 10 = 3 ∧
    acceleratedOrbit 10 20 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_20 : gap 10 20 = 997 ∧ 27 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_20 : threshold 10 20 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_20 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 20) = 27 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 20
  rw [data_10_20.1, data_10_20.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_20 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 20) = 27 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 20
  rw [data_10_20.1, data_10_20.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_20 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 20) < 1024 * (2 * m) + 20 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 20 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_20] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 20) < 1024 * (2 * m) + 20 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_20 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 20) < 1024 * (2 * m + 1) + 20 := by
  apply refinement_cleared (k := 10) (r := 20) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_20]; decide

end Collatz.Research.RefinementAtlas.Batch267
