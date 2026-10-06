import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 237. -/
namespace Collatz.Research.RefinementAtlas.Batch237
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 399). -/
theorem data_9_399 : oddCount 399 9 = 5 ∧
    acceleratedOrbit 9 399 = 190 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_399 : gap 9 399 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_399 : threshold 9 399 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_399 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 399) = 243 * (2 * m) + 190 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 399
  rw [data_9_399.1, data_9_399.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_399 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 399) = 243 * (2 * m + 1) + 190 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 399
  rw [data_9_399.1, data_9_399.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_399 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 399) < 512 * (2 * m) + 399 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 399 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_399] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 399) < 512 * (2 * m) + 399 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_399 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 399) < 512 * (2 * m + 1) + 399 := by
  apply refinement_cleared (k := 9) (r := 399) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_399]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 400). -/
theorem data_9_400 : oddCount 400 9 = 3 ∧
    acceleratedOrbit 9 400 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_400 : gap 9 400 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_400 : threshold 9 400 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_400 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 400) = 27 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 400
  rw [data_9_400.1, data_9_400.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_400 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 400) = 27 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 400
  rw [data_9_400.1, data_9_400.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_400 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 400) < 512 * (2 * m) + 400 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 400 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_400] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 400) < 512 * (2 * m) + 400 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_400 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 400) < 512 * (2 * m + 1) + 400 := by
  apply refinement_cleared (k := 9) (r := 400) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_400]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 401). -/
theorem data_9_401 : oddCount 401 9 = 4 ∧
    acceleratedOrbit 9 401 = 64 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_401 : gap 9 401 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_401 : threshold 9 401 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_401 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 401) = 81 * (2 * m) + 64 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 401
  rw [data_9_401.1, data_9_401.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_401 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 401) = 81 * (2 * m + 1) + 64 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 401
  rw [data_9_401.1, data_9_401.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_401 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 401) < 512 * (2 * m) + 401 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 401 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_401] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 401) < 512 * (2 * m) + 401 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_401 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 401) < 512 * (2 * m + 1) + 401 := by
  apply refinement_cleared (k := 9) (r := 401) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_401]; decide

end Collatz.Research.RefinementAtlas.Batch237
