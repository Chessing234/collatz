import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 252. -/
namespace Collatz.Research.RefinementAtlas.Batch252
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 459). -/
theorem data_9_459 : oddCount 459 9 = 4 ∧
    acceleratedOrbit 9 459 = 73 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_459 : gap 9 459 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_459 : threshold 9 459 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_459 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 459) = 81 * (2 * m) + 73 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 459
  rw [data_9_459.1, data_9_459.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_459 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 459) = 81 * (2 * m + 1) + 73 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 459
  rw [data_9_459.1, data_9_459.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_459 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 459) < 512 * (2 * m) + 459 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 459 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_459] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 459) < 512 * (2 * m) + 459 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_459 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 459) < 512 * (2 * m + 1) + 459 := by
  apply refinement_cleared (k := 9) (r := 459) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_459]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 460). -/
theorem data_9_460 : oddCount 460 9 = 4 ∧
    acceleratedOrbit 9 460 = 74 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_460 : gap 9 460 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_460 : threshold 9 460 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_460 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 460) = 81 * (2 * m) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 460
  rw [data_9_460.1, data_9_460.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_460 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 460) = 81 * (2 * m + 1) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 460
  rw [data_9_460.1, data_9_460.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_460 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 460) < 512 * (2 * m) + 460 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 460 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_460] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 460) < 512 * (2 * m) + 460 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_460 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 460) < 512 * (2 * m + 1) + 460 := by
  apply refinement_cleared (k := 9) (r := 460) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_460]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 461). -/
theorem data_9_461 : oddCount 461 9 = 4 ∧
    acceleratedOrbit 9 461 = 74 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_461 : gap 9 461 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_461 : threshold 9 461 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_461 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 461) = 81 * (2 * m) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 461
  rw [data_9_461.1, data_9_461.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_461 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 461) = 81 * (2 * m + 1) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 461
  rw [data_9_461.1, data_9_461.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_461 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 461) < 512 * (2 * m) + 461 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 461 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_461] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 461) < 512 * (2 * m) + 461 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_461 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 461) < 512 * (2 * m + 1) + 461 := by
  apply refinement_cleared (k := 9) (r := 461) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_461]; decide

end Collatz.Research.RefinementAtlas.Batch252
