import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 196. -/
namespace Collatz.Research.RefinementAtlas.Batch196
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 237). -/
theorem data_9_237 : oddCount 237 9 = 4 ∧
    acceleratedOrbit 9 237 = 38 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_237 : gap 9 237 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_237 : threshold 9 237 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_237 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 237) = 81 * (2 * m) + 38 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 237
  rw [data_9_237.1, data_9_237.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_237 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 237) = 81 * (2 * m + 1) + 38 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 237
  rw [data_9_237.1, data_9_237.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_237 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 237) < 512 * (2 * m) + 237 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 237 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_237] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 237) < 512 * (2 * m) + 237 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_237 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 237) < 512 * (2 * m + 1) + 237 := by
  apply refinement_cleared (k := 9) (r := 237) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_237]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 238). -/
theorem data_9_238 : oddCount 238 9 = 4 ∧
    acceleratedOrbit 9 238 = 38 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_238 : gap 9 238 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_238 : threshold 9 238 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_238 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 238) = 81 * (2 * m) + 38 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 238
  rw [data_9_238.1, data_9_238.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_238 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 238) = 81 * (2 * m + 1) + 38 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 238
  rw [data_9_238.1, data_9_238.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_238 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 238) < 512 * (2 * m) + 238 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 238 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_238] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 238) < 512 * (2 * m) + 238 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_238 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 238) < 512 * (2 * m + 1) + 238 := by
  apply refinement_cleared (k := 9) (r := 238) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_238]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 240). -/
theorem data_9_240 : oddCount 240 9 = 4 ∧
    acceleratedOrbit 9 240 = 40 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_240 : gap 9 240 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_240 : threshold 9 240 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_240 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 240) = 81 * (2 * m) + 40 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 240
  rw [data_9_240.1, data_9_240.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_240 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 240) = 81 * (2 * m + 1) + 40 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 240
  rw [data_9_240.1, data_9_240.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_240 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 240) < 512 * (2 * m) + 240 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 240 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_240] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 240) < 512 * (2 * m) + 240 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_240 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 240) < 512 * (2 * m + 1) + 240 := by
  apply refinement_cleared (k := 9) (r := 240) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_240]; decide

end Collatz.Research.RefinementAtlas.Batch196
