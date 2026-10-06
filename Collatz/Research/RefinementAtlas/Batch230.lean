import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 230. -/
namespace Collatz.Research.RefinementAtlas.Batch230
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 372). -/
theorem data_9_372 : oddCount 372 9 = 3 ∧
    acceleratedOrbit 9 372 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_372 : gap 9 372 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_372 : threshold 9 372 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_372 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 372) = 27 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 372
  rw [data_9_372.1, data_9_372.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_372 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 372) = 27 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 372
  rw [data_9_372.1, data_9_372.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_372 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 372) < 512 * (2 * m) + 372 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 372 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_372] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 372) < 512 * (2 * m) + 372 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_372 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 372) < 512 * (2 * m + 1) + 372 := by
  apply refinement_cleared (k := 9) (r := 372) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_372]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 373). -/
theorem data_9_373 : oddCount 373 9 = 3 ∧
    acceleratedOrbit 9 373 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_373 : gap 9 373 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_373 : threshold 9 373 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_373 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 373) = 27 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 373
  rw [data_9_373.1, data_9_373.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_373 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 373) = 27 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 373
  rw [data_9_373.1, data_9_373.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_373 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 373) < 512 * (2 * m) + 373 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 373 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_373] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 373) < 512 * (2 * m) + 373 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_373 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 373) < 512 * (2 * m + 1) + 373 := by
  apply refinement_cleared (k := 9) (r := 373) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_373]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 374). -/
theorem data_9_374 : oddCount 374 9 = 5 ∧
    acceleratedOrbit 9 374 = 179 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_374 : gap 9 374 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_374 : threshold 9 374 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_374 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 374) = 243 * (2 * m) + 179 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 374
  rw [data_9_374.1, data_9_374.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_374 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 374) = 243 * (2 * m + 1) + 179 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 374
  rw [data_9_374.1, data_9_374.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_374 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 374) < 512 * (2 * m) + 374 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 374 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_374] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 374) < 512 * (2 * m) + 374 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_374 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 374) < 512 * (2 * m + 1) + 374 := by
  apply refinement_cleared (k := 9) (r := 374) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_374]; decide

end Collatz.Research.RefinementAtlas.Batch230
