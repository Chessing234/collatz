import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 204. -/
namespace Collatz.Research.RefinementAtlas.Batch204
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 271). -/
theorem data_9_271 : oddCount 271 9 = 4 ∧
    acceleratedOrbit 9 271 = 43 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_271 : gap 9 271 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_271 : threshold 9 271 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_271 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 271) = 81 * (2 * m) + 43 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 271
  rw [data_9_271.1, data_9_271.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_271 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 271) = 81 * (2 * m + 1) + 43 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 271
  rw [data_9_271.1, data_9_271.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_271 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 271) < 512 * (2 * m) + 271 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 271 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_271] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 271) < 512 * (2 * m) + 271 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_271 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 271) < 512 * (2 * m + 1) + 271 := by
  apply refinement_cleared (k := 9) (r := 271) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_271]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 272). -/
theorem data_9_272 : oddCount 272 9 = 2 ∧
    acceleratedOrbit 9 272 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_272 : gap 9 272 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_272 : threshold 9 272 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_272 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 272) = 9 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 272
  rw [data_9_272.1, data_9_272.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_272 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 272) = 9 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 272
  rw [data_9_272.1, data_9_272.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_272 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 272) < 512 * (2 * m) + 272 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 272 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_272] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 272) < 512 * (2 * m) + 272 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_272 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 272) < 512 * (2 * m + 1) + 272 := by
  apply refinement_cleared (k := 9) (r := 272) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_272]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 273). -/
theorem data_9_273 : oddCount 273 9 = 4 ∧
    acceleratedOrbit 9 273 = 44 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_273 : gap 9 273 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_273 : threshold 9 273 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_273 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 273) = 81 * (2 * m) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 273
  rw [data_9_273.1, data_9_273.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_273 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 273) = 81 * (2 * m + 1) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 273
  rw [data_9_273.1, data_9_273.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_273 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 273) < 512 * (2 * m) + 273 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 273 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_273] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 273) < 512 * (2 * m) + 273 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_273 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 273) < 512 * (2 * m + 1) + 273 := by
  apply refinement_cleared (k := 9) (r := 273) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_273]; decide

end Collatz.Research.RefinementAtlas.Batch204
