import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 026. -/
namespace Collatz.Research.RefinementAtlas.Batch026
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (6, 29). -/
theorem data_6_29 : oddCount 29 6 = 3 ∧
    acceleratedOrbit 6 29 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_29 : gap 6 29 = 37 ∧ 27 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_29 : threshold 6 29 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_29 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 29) = 27 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 29
  rw [data_6_29.1, data_6_29.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_29 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 29) = 27 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 29
  rw [data_6_29.1, data_6_29.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_29 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 29) < 64 * (2 * m) + 29 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 29 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_29] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 29) < 64 * (2 * m) + 29 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_29 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 29) < 64 * (2 * m + 1) + 29 := by
  apply refinement_cleared (k := 6) (r := 29) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_29]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 32). -/
theorem data_6_32 : oddCount 32 6 = 1 ∧
    acceleratedOrbit 6 32 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_32 : gap 6 32 = 61 ∧ 3 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_32 : threshold 6 32 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_32 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 32) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 32
  rw [data_6_32.1, data_6_32.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_32 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 32) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 32
  rw [data_6_32.1, data_6_32.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_32 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 32) < 64 * (2 * m) + 32 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 32 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_32] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 32) < 64 * (2 * m) + 32 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_32 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 32) < 64 * (2 * m + 1) + 32 := by
  apply refinement_cleared (k := 6) (r := 32) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_32]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 34). -/
theorem data_6_34 : oddCount 34 6 = 2 ∧
    acceleratedOrbit 6 34 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_34 : gap 6 34 = 55 ∧ 9 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_34 : threshold 6 34 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_34 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 34) = 9 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 34
  rw [data_6_34.1, data_6_34.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_34 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 34) = 9 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 34
  rw [data_6_34.1, data_6_34.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_34 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 34) < 64 * (2 * m) + 34 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 34 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_34] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 34) < 64 * (2 * m) + 34 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_34 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 34) < 64 * (2 * m + 1) + 34 := by
  apply refinement_cleared (k := 6) (r := 34) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_34]; decide

end Collatz.Research.RefinementAtlas.Batch026
