import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 150. -/
namespace Collatz.Research.RefinementAtlas.Batch150
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 50). -/
theorem data_9_50 : oddCount 50 9 = 5 ∧
    acceleratedOrbit 9 50 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_50 : gap 9 50 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_50 : threshold 9 50 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_50 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 50) = 243 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 50
  rw [data_9_50.1, data_9_50.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_50 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 50) = 243 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 50
  rw [data_9_50.1, data_9_50.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_50 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 50) < 512 * (2 * m) + 50 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 50 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_50] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 50) < 512 * (2 * m) + 50 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_50 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 50) < 512 * (2 * m + 1) + 50 := by
  apply refinement_cleared (k := 9) (r := 50) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_50]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 51). -/
theorem data_9_51 : oddCount 51 9 = 5 ∧
    acceleratedOrbit 9 51 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_51 : gap 9 51 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_51 : threshold 9 51 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_51 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 51) = 243 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 51
  rw [data_9_51.1, data_9_51.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_51 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 51) = 243 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 51
  rw [data_9_51.1, data_9_51.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_51 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 51) < 512 * (2 * m) + 51 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 51 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_51] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 51) < 512 * (2 * m) + 51 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_51 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 51) < 512 * (2 * m + 1) + 51 := by
  apply refinement_cleared (k := 9) (r := 51) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_51]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 52). -/
theorem data_9_52 : oddCount 52 9 = 2 ∧
    acceleratedOrbit 9 52 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_52 : gap 9 52 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_52 : threshold 9 52 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_52 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 52) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 52
  rw [data_9_52.1, data_9_52.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_52 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 52) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 52
  rw [data_9_52.1, data_9_52.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_52 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 52) < 512 * (2 * m) + 52 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 52 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_52] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 52) < 512 * (2 * m) + 52 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_52 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 52) < 512 * (2 * m + 1) + 52 := by
  apply refinement_cleared (k := 9) (r := 52) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_52]; decide

end Collatz.Research.RefinementAtlas.Batch150
