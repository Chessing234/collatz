import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 231. -/
namespace Collatz.Research.RefinementAtlas.Batch231
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 375). -/
theorem data_9_375 : oddCount 375 9 = 5 ∧
    acceleratedOrbit 9 375 = 179 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_375 : gap 9 375 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_375 : threshold 9 375 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_375 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 375) = 243 * (2 * m) + 179 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 375
  rw [data_9_375.1, data_9_375.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_375 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 375) = 243 * (2 * m + 1) + 179 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 375
  rw [data_9_375.1, data_9_375.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_375 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 375) < 512 * (2 * m) + 375 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 375 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_375] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 375) < 512 * (2 * m) + 375 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_375 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 375) < 512 * (2 * m + 1) + 375 := by
  apply refinement_cleared (k := 9) (r := 375) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_375]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 376). -/
theorem data_9_376 : oddCount 376 9 = 5 ∧
    acceleratedOrbit 9 376 = 182 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_376 : gap 9 376 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_376 : threshold 9 376 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_376 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 376) = 243 * (2 * m) + 182 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 376
  rw [data_9_376.1, data_9_376.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_376 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 376) = 243 * (2 * m + 1) + 182 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 376
  rw [data_9_376.1, data_9_376.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_376 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 376) < 512 * (2 * m) + 376 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 376 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_376] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 376) < 512 * (2 * m) + 376 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_376 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 376) < 512 * (2 * m + 1) + 376 := by
  apply refinement_cleared (k := 9) (r := 376) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_376]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 378). -/
theorem data_9_378 : oddCount 378 9 = 5 ∧
    acceleratedOrbit 9 378 = 182 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_378 : gap 9 378 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_378 : threshold 9 378 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_378 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 378) = 243 * (2 * m) + 182 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 378
  rw [data_9_378.1, data_9_378.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_378 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 378) = 243 * (2 * m + 1) + 182 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 378
  rw [data_9_378.1, data_9_378.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_378 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 378) < 512 * (2 * m) + 378 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 378 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_378] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 378) < 512 * (2 * m) + 378 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_378 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 378) < 512 * (2 * m + 1) + 378 := by
  apply refinement_cleared (k := 9) (r := 378) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_378]; decide

end Collatz.Research.RefinementAtlas.Batch231
