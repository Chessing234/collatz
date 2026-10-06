import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 168. -/
namespace Collatz.Research.RefinementAtlas.Batch168
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 123). -/
theorem data_9_123 : oddCount 123 9 = 5 ∧
    acceleratedOrbit 9 123 = 59 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_123 : gap 9 123 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_123 : threshold 9 123 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_123 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 123) = 243 * (2 * m) + 59 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 123
  rw [data_9_123.1, data_9_123.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_123 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 123) = 243 * (2 * m + 1) + 59 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 123
  rw [data_9_123.1, data_9_123.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_123 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 123) < 512 * (2 * m) + 123 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 123 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_123] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 123) < 512 * (2 * m) + 123 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_123 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 123) < 512 * (2 * m + 1) + 123 := by
  apply refinement_cleared (k := 9) (r := 123) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_123]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 128). -/
theorem data_9_128 : oddCount 128 9 = 1 ∧
    acceleratedOrbit 9 128 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_128 : gap 9 128 = 509 ∧ 3 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_128 : threshold 9 128 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_128 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 128) = 3 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 128
  rw [data_9_128.1, data_9_128.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_128 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 128) = 3 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 128
  rw [data_9_128.1, data_9_128.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_128 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 128) < 512 * (2 * m) + 128 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 128 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_128] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 128) < 512 * (2 * m) + 128 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_128 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 128) < 512 * (2 * m + 1) + 128 := by
  apply refinement_cleared (k := 9) (r := 128) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_128]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 130). -/
theorem data_9_130 : oddCount 130 9 = 3 ∧
    acceleratedOrbit 9 130 = 7 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_130 : gap 9 130 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_130 : threshold 9 130 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_130 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 130) = 27 * (2 * m) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 130
  rw [data_9_130.1, data_9_130.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_130 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 130) = 27 * (2 * m + 1) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 130
  rw [data_9_130.1, data_9_130.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_130 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 130) < 512 * (2 * m) + 130 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 130 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_130] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 130) < 512 * (2 * m) + 130 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_130 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 130) < 512 * (2 * m + 1) + 130 := by
  apply refinement_cleared (k := 9) (r := 130) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_130]; decide

end Collatz.Research.RefinementAtlas.Batch168
