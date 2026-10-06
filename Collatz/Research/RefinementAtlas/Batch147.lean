import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 147. -/
namespace Collatz.Research.RefinementAtlas.Batch147
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 39). -/
theorem data_9_39 : oddCount 39 9 = 5 ∧
    acceleratedOrbit 9 39 = 19 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_39 : gap 9 39 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_39 : threshold 9 39 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_39 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 39) = 243 * (2 * m) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 39
  rw [data_9_39.1, data_9_39.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_39 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 39) = 243 * (2 * m + 1) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 39
  rw [data_9_39.1, data_9_39.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_39 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 39) < 512 * (2 * m) + 39 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 39 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_39] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 39) < 512 * (2 * m) + 39 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_39 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 39) < 512 * (2 * m + 1) + 39 := by
  apply refinement_cleared (k := 9) (r := 39) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_39]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 40). -/
theorem data_9_40 : oddCount 40 9 = 2 ∧
    acceleratedOrbit 9 40 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_40 : gap 9 40 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_40 : threshold 9 40 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_40 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 40) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 40
  rw [data_9_40.1, data_9_40.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_40 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 40) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 40
  rw [data_9_40.1, data_9_40.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_40 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 40) < 512 * (2 * m) + 40 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 40 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_40] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 40) < 512 * (2 * m) + 40 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_40 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 40) < 512 * (2 * m + 1) + 40 := by
  apply refinement_cleared (k := 9) (r := 40) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_40]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 42). -/
theorem data_9_42 : oddCount 42 9 = 2 ∧
    acceleratedOrbit 9 42 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_42 : gap 9 42 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_42 : threshold 9 42 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_42 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 42) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 42
  rw [data_9_42.1, data_9_42.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_42 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 42) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 42
  rw [data_9_42.1, data_9_42.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_42 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 42) < 512 * (2 * m) + 42 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 42 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_42] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 42) < 512 * (2 * m) + 42 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_42 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 42) < 512 * (2 * m + 1) + 42 := by
  apply refinement_cleared (k := 9) (r := 42) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_42]; decide

end Collatz.Research.RefinementAtlas.Batch147
