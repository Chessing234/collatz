import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 160. -/
namespace Collatz.Research.RefinementAtlas.Batch160
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 88). -/
theorem data_9_88 : oddCount 88 9 = 3 ∧
    acceleratedOrbit 9 88 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_88 : gap 9 88 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_88 : threshold 9 88 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_88 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 88) = 27 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 88
  rw [data_9_88.1, data_9_88.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_88 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 88) = 27 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 88
  rw [data_9_88.1, data_9_88.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_88 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 88) < 512 * (2 * m) + 88 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 88 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_88] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 88) < 512 * (2 * m) + 88 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_88 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 88) < 512 * (2 * m + 1) + 88 := by
  apply refinement_cleared (k := 9) (r := 88) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_88]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 89). -/
theorem data_9_89 : oddCount 89 9 = 5 ∧
    acceleratedOrbit 9 89 = 44 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_89 : gap 9 89 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_89 : threshold 9 89 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_89 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 89) = 243 * (2 * m) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 89
  rw [data_9_89.1, data_9_89.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_89 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 89) = 243 * (2 * m + 1) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 89
  rw [data_9_89.1, data_9_89.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_89 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 89) < 512 * (2 * m) + 89 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 89 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_89] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 89) < 512 * (2 * m) + 89 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_89 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 89) < 512 * (2 * m + 1) + 89 := by
  apply refinement_cleared (k := 9) (r := 89) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_89]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 90). -/
theorem data_9_90 : oddCount 90 9 = 3 ∧
    acceleratedOrbit 9 90 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_90 : gap 9 90 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_90 : threshold 9 90 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_90 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 90) = 27 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 90
  rw [data_9_90.1, data_9_90.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_90 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 90) = 27 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 90
  rw [data_9_90.1, data_9_90.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_90 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 90) < 512 * (2 * m) + 90 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 90 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_90] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 90) < 512 * (2 * m) + 90 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_90 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 90) < 512 * (2 * m + 1) + 90 := by
  apply refinement_cleared (k := 9) (r := 90) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_90]; decide

end Collatz.Research.RefinementAtlas.Batch160
