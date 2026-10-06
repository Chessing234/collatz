import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 158. -/
namespace Collatz.Research.RefinementAtlas.Batch158
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 80). -/
theorem data_9_80 : oddCount 80 9 = 2 ∧
    acceleratedOrbit 9 80 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_80 : gap 9 80 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_80 : threshold 9 80 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_80 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 80) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 80
  rw [data_9_80.1, data_9_80.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_80 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 80) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 80
  rw [data_9_80.1, data_9_80.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_80 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 80) < 512 * (2 * m) + 80 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 80 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_80] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 80) < 512 * (2 * m) + 80 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_80 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 80) < 512 * (2 * m + 1) + 80 := by
  apply refinement_cleared (k := 9) (r := 80) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_80]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 81). -/
theorem data_9_81 : oddCount 81 9 = 5 ∧
    acceleratedOrbit 9 81 = 40 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_81 : gap 9 81 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_81 : threshold 9 81 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_81 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 81) = 243 * (2 * m) + 40 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 81
  rw [data_9_81.1, data_9_81.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_81 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 81) = 243 * (2 * m + 1) + 40 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 81
  rw [data_9_81.1, data_9_81.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_81 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 81) < 512 * (2 * m) + 81 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 81 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_81] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 81) < 512 * (2 * m) + 81 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_81 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 81) < 512 * (2 * m + 1) + 81 := by
  apply refinement_cleared (k := 9) (r := 81) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_81]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 84). -/
theorem data_9_84 : oddCount 84 9 = 2 ∧
    acceleratedOrbit 9 84 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_84 : gap 9 84 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_84 : threshold 9 84 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_84 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 84) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 84
  rw [data_9_84.1, data_9_84.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_84 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 84) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 84
  rw [data_9_84.1, data_9_84.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_84 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 84) < 512 * (2 * m) + 84 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 84 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_84] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 84) < 512 * (2 * m) + 84 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_84 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 84) < 512 * (2 * m + 1) + 84 := by
  apply refinement_cleared (k := 9) (r := 84) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_84]; decide

end Collatz.Research.RefinementAtlas.Batch158
