import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 146. -/
namespace Collatz.Research.RefinementAtlas.Batch146
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 36). -/
theorem data_9_36 : oddCount 36 9 = 5 ∧
    acceleratedOrbit 9 36 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_36 : gap 9 36 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_36 : threshold 9 36 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_36 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 36) = 243 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 36
  rw [data_9_36.1, data_9_36.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_36 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 36) = 243 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 36
  rw [data_9_36.1, data_9_36.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_36 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 36) < 512 * (2 * m) + 36 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 36 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_36] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 36) < 512 * (2 * m) + 36 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_36 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 36) < 512 * (2 * m + 1) + 36 := by
  apply refinement_cleared (k := 9) (r := 36) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_36]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 37). -/
theorem data_9_37 : oddCount 37 9 = 5 ∧
    acceleratedOrbit 9 37 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_37 : gap 9 37 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_37 : threshold 9 37 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_37 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 37) = 243 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 37
  rw [data_9_37.1, data_9_37.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_37 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 37) = 243 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 37
  rw [data_9_37.1, data_9_37.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_37 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 37) < 512 * (2 * m) + 37 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 37 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_37] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 37) < 512 * (2 * m) + 37 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_37 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 37) < 512 * (2 * m + 1) + 37 := by
  apply refinement_cleared (k := 9) (r := 37) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_37]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 38). -/
theorem data_9_38 : oddCount 38 9 = 5 ∧
    acceleratedOrbit 9 38 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_38 : gap 9 38 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_38 : threshold 9 38 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_38 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 38) = 243 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 38
  rw [data_9_38.1, data_9_38.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_38 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 38) = 243 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 38
  rw [data_9_38.1, data_9_38.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_38 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 38) < 512 * (2 * m) + 38 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 38 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_38] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 38) < 512 * (2 * m) + 38 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_38 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 38) < 512 * (2 * m + 1) + 38 := by
  apply refinement_cleared (k := 9) (r := 38) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_38]; decide

end Collatz.Research.RefinementAtlas.Batch146
