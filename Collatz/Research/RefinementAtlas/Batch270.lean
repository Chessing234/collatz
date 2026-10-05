import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 270. -/
namespace Collatz.Research.RefinementAtlas.Batch270
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 28). -/
theorem data_10_28 : oddCount 28 10 = 5 ∧
    acceleratedOrbit 10 28 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_28 : gap 10 28 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_28 : threshold 10 28 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_28 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 28) = 243 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 28
  rw [data_10_28.1, data_10_28.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_28 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 28) = 243 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 28
  rw [data_10_28.1, data_10_28.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_28 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 28) < 1024 * (2 * m) + 28 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 28 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_28] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 28) < 1024 * (2 * m) + 28 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_28 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 28) < 1024 * (2 * m + 1) + 28 := by
  apply refinement_cleared (k := 10) (r := 28) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_28]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 29). -/
theorem data_10_29 : oddCount 29 10 = 5 ∧
    acceleratedOrbit 10 29 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_29 : gap 10 29 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_29 : threshold 10 29 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_29 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 29) = 243 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 29
  rw [data_10_29.1, data_10_29.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_29 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 29) = 243 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 29
  rw [data_10_29.1, data_10_29.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_29 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 29) < 1024 * (2 * m) + 29 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 29 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_29] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 29) < 1024 * (2 * m) + 29 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_29 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 29) < 1024 * (2 * m + 1) + 29 := by
  apply refinement_cleared (k := 10) (r := 29) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_29]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 30). -/
theorem data_10_30 : oddCount 30 10 = 5 ∧
    acceleratedOrbit 10 30 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_30 : gap 10 30 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_30 : threshold 10 30 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_30 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 30) = 243 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 30
  rw [data_10_30.1, data_10_30.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_30 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 30) = 243 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 30
  rw [data_10_30.1, data_10_30.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_30 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 30) < 1024 * (2 * m) + 30 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 30 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_30] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 30) < 1024 * (2 * m) + 30 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_30 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 30) < 1024 * (2 * m + 1) + 30 := by
  apply refinement_cleared (k := 10) (r := 30) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_30]; decide

end Collatz.Research.RefinementAtlas.Batch270
