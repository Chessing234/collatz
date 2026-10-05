import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 149. -/
namespace Collatz.Research.RefinementAtlas.Batch149
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 46). -/
theorem data_9_46 : oddCount 46 9 = 4 ∧
    acceleratedOrbit 9 46 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_46 : gap 9 46 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_46 : threshold 9 46 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_46 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 46) = 81 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 46
  rw [data_9_46.1, data_9_46.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_46 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 46) = 81 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 46
  rw [data_9_46.1, data_9_46.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_46 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 46) < 512 * (2 * m) + 46 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 46 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_46] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 46) < 512 * (2 * m) + 46 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_46 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 46) < 512 * (2 * m + 1) + 46 := by
  apply refinement_cleared (k := 9) (r := 46) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_46]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 48). -/
theorem data_9_48 : oddCount 48 9 = 2 ∧
    acceleratedOrbit 9 48 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_48 : gap 9 48 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_48 : threshold 9 48 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_48 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 48) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 48
  rw [data_9_48.1, data_9_48.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_48 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 48) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 48
  rw [data_9_48.1, data_9_48.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_48 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 48) < 512 * (2 * m) + 48 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 48 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_48] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 48) < 512 * (2 * m) + 48 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_48 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 48) < 512 * (2 * m + 1) + 48 := by
  apply refinement_cleared (k := 9) (r := 48) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_48]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 49). -/
theorem data_9_49 : oddCount 49 9 = 5 ∧
    acceleratedOrbit 9 49 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_49 : gap 9 49 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_49 : threshold 9 49 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_49 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 49) = 243 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 49
  rw [data_9_49.1, data_9_49.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_49 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 49) = 243 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 49
  rw [data_9_49.1, data_9_49.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_49 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 49) < 512 * (2 * m) + 49 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 49 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_49] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 49) < 512 * (2 * m) + 49 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_49 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 49) < 512 * (2 * m + 1) + 49 := by
  apply refinement_cleared (k := 9) (r := 49) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_49]; decide

end Collatz.Research.RefinementAtlas.Batch149
