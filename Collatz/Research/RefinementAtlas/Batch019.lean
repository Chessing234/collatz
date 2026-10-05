import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 019. -/
namespace Collatz.Research.RefinementAtlas.Batch019
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (5, 28). -/
theorem data_5_28 : oddCount 28 5 = 3 ∧
    acceleratedOrbit 5 28 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_28 : gap 5 28 = 5 ∧ 27 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_28 : threshold 5 28 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_28 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 28) = 27 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 28
  rw [data_5_28.1, data_5_28.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_28 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 28) = 27 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 28
  rw [data_5_28.1, data_5_28.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_28 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 28) < 32 * (2 * m) + 28 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 28 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_28] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 28) < 32 * (2 * m) + 28 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_28 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 28) < 32 * (2 * m + 1) + 28 := by
  apply refinement_cleared (k := 5) (r := 28) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_28]; decide

/-- Kernel-evaluated parity count and endpoint for (5, 29). -/
theorem data_5_29 : oddCount 29 5 = 3 ∧
    acceleratedOrbit 5 29 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_29 : gap 5 29 = 5 ∧ 27 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_29 : threshold 5 29 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_29 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 29) = 27 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 29
  rw [data_5_29.1, data_5_29.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_29 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 29) = 27 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 29
  rw [data_5_29.1, data_5_29.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_29 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 29) < 32 * (2 * m) + 29 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 29 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_29] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 29) < 32 * (2 * m) + 29 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_29 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 29) < 32 * (2 * m + 1) + 29 := by
  apply refinement_cleared (k := 5) (r := 29) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_29]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 3). -/
theorem data_6_3 : oddCount 3 6 = 3 ∧
    acceleratedOrbit 6 3 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_3 : gap 6 3 = 37 ∧ 27 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_3 : threshold 6 3 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_3 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 3) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 3
  rw [data_6_3.1, data_6_3.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_3 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 3) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 3
  rw [data_6_3.1, data_6_3.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_3 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 3) < 64 * (2 * m) + 3 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 3 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_3] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 3) < 64 * (2 * m) + 3 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_3 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 3) < 64 * (2 * m + 1) + 3 := by
  apply refinement_cleared (k := 6) (r := 3) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_3]; decide

end Collatz.Research.RefinementAtlas.Batch019
