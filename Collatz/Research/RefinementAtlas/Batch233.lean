import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 233. -/
namespace Collatz.Research.RefinementAtlas.Batch233
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 385). -/
theorem data_9_385 : oddCount 385 9 = 5 ∧
    acceleratedOrbit 9 385 = 184 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_385 : gap 9 385 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_385 : threshold 9 385 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_385 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 385) = 243 * (2 * m) + 184 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 385
  rw [data_9_385.1, data_9_385.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_385 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 385) = 243 * (2 * m + 1) + 184 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 385
  rw [data_9_385.1, data_9_385.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_385 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 385) < 512 * (2 * m) + 385 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 385 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_385] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 385) < 512 * (2 * m) + 385 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_385 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 385) < 512 * (2 * m + 1) + 385 := by
  apply refinement_cleared (k := 9) (r := 385) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_385]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 386). -/
theorem data_9_386 : oddCount 386 9 = 4 ∧
    acceleratedOrbit 9 386 = 62 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_386 : gap 9 386 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_386 : threshold 9 386 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_386 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 386) = 81 * (2 * m) + 62 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 386
  rw [data_9_386.1, data_9_386.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_386 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 386) = 81 * (2 * m + 1) + 62 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 386
  rw [data_9_386.1, data_9_386.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_386 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 386) < 512 * (2 * m) + 386 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 386 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_386] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 386) < 512 * (2 * m) + 386 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_386 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 386) < 512 * (2 * m + 1) + 386 := by
  apply refinement_cleared (k := 9) (r := 386) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_386]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 387). -/
theorem data_9_387 : oddCount 387 9 = 4 ∧
    acceleratedOrbit 9 387 = 62 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_387 : gap 9 387 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_387 : threshold 9 387 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_387 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 387) = 81 * (2 * m) + 62 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 387
  rw [data_9_387.1, data_9_387.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_387 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 387) = 81 * (2 * m + 1) + 62 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 387
  rw [data_9_387.1, data_9_387.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_387 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 387) < 512 * (2 * m) + 387 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 387 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_387] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 387) < 512 * (2 * m) + 387 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_387 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 387) < 512 * (2 * m + 1) + 387 := by
  apply refinement_cleared (k := 9) (r := 387) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_387]; decide

end Collatz.Research.RefinementAtlas.Batch233
