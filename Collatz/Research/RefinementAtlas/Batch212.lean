import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 212. -/
namespace Collatz.Research.RefinementAtlas.Batch212
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 302). -/
theorem data_9_302 : oddCount 302 9 = 3 ∧
    acceleratedOrbit 9 302 = 16 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_302 : gap 9 302 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_302 : threshold 9 302 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_302 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 302) = 27 * (2 * m) + 16 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 302
  rw [data_9_302.1, data_9_302.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_302 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 302) = 27 * (2 * m + 1) + 16 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 302
  rw [data_9_302.1, data_9_302.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_302 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 302) < 512 * (2 * m) + 302 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 302 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_302] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 302) < 512 * (2 * m) + 302 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_302 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 302) < 512 * (2 * m + 1) + 302 := by
  apply refinement_cleared (k := 9) (r := 302) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_302]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 304). -/
theorem data_9_304 : oddCount 304 9 = 3 ∧
    acceleratedOrbit 9 304 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_304 : gap 9 304 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_304 : threshold 9 304 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_304 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 304) = 27 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 304
  rw [data_9_304.1, data_9_304.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_304 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 304) = 27 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 304
  rw [data_9_304.1, data_9_304.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_304 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 304) < 512 * (2 * m) + 304 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 304 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_304] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 304) < 512 * (2 * m) + 304 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_304 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 304) < 512 * (2 * m + 1) + 304 := by
  apply refinement_cleared (k := 9) (r := 304) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_304]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 305). -/
theorem data_9_305 : oddCount 305 9 = 4 ∧
    acceleratedOrbit 9 305 = 49 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_305 : gap 9 305 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_305 : threshold 9 305 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_305 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 305) = 81 * (2 * m) + 49 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 305
  rw [data_9_305.1, data_9_305.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_305 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 305) = 81 * (2 * m + 1) + 49 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 305
  rw [data_9_305.1, data_9_305.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_305 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 305) < 512 * (2 * m) + 305 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 305 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_305] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 305) < 512 * (2 * m) + 305 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_305 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 305) < 512 * (2 * m + 1) + 305 := by
  apply refinement_cleared (k := 9) (r := 305) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_305]; decide

end Collatz.Research.RefinementAtlas.Batch212
