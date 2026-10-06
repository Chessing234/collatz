import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 232. -/
namespace Collatz.Research.RefinementAtlas.Batch232
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 380). -/
theorem data_9_380 : oddCount 380 9 = 5 ∧
    acceleratedOrbit 9 380 = 182 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_380 : gap 9 380 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_380 : threshold 9 380 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_380 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 380) = 243 * (2 * m) + 182 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 380
  rw [data_9_380.1, data_9_380.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_380 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 380) = 243 * (2 * m + 1) + 182 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 380
  rw [data_9_380.1, data_9_380.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_380 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 380) < 512 * (2 * m) + 380 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 380 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_380] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 380) < 512 * (2 * m) + 380 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_380 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 380) < 512 * (2 * m + 1) + 380 := by
  apply refinement_cleared (k := 9) (r := 380) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_380]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 381). -/
theorem data_9_381 : oddCount 381 9 = 5 ∧
    acceleratedOrbit 9 381 = 182 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_381 : gap 9 381 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_381 : threshold 9 381 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_381 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 381) = 243 * (2 * m) + 182 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 381
  rw [data_9_381.1, data_9_381.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_381 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 381) = 243 * (2 * m + 1) + 182 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 381
  rw [data_9_381.1, data_9_381.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_381 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 381) < 512 * (2 * m) + 381 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 381 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_381] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 381) < 512 * (2 * m) + 381 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_381 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 381) < 512 * (2 * m + 1) + 381 := by
  apply refinement_cleared (k := 9) (r := 381) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_381]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 384). -/
theorem data_9_384 : oddCount 384 9 = 2 ∧
    acceleratedOrbit 9 384 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_384 : gap 9 384 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_384 : threshold 9 384 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_384 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 384) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 384
  rw [data_9_384.1, data_9_384.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_384 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 384) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 384
  rw [data_9_384.1, data_9_384.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_384 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 384) < 512 * (2 * m) + 384 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 384 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_384] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 384) < 512 * (2 * m) + 384 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_384 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 384) < 512 * (2 * m + 1) + 384 := by
  apply refinement_cleared (k := 9) (r := 384) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_384]; decide

end Collatz.Research.RefinementAtlas.Batch232
