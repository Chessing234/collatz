import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 148. -/
namespace Collatz.Research.RefinementAtlas.Batch148
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 43). -/
theorem data_9_43 : oddCount 43 9 = 4 ∧
    acceleratedOrbit 9 43 = 7 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_43 : gap 9 43 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_43 : threshold 9 43 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_43 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 43) = 81 * (2 * m) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 43
  rw [data_9_43.1, data_9_43.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_43 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 43) = 81 * (2 * m + 1) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 43
  rw [data_9_43.1, data_9_43.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_43 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 43) < 512 * (2 * m) + 43 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 43 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_43] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 43) < 512 * (2 * m) + 43 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_43 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 43) < 512 * (2 * m + 1) + 43 := by
  apply refinement_cleared (k := 9) (r := 43) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_43]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 44). -/
theorem data_9_44 : oddCount 44 9 = 4 ∧
    acceleratedOrbit 9 44 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_44 : gap 9 44 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_44 : threshold 9 44 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_44 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 44) = 81 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 44
  rw [data_9_44.1, data_9_44.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_44 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 44) = 81 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 44
  rw [data_9_44.1, data_9_44.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_44 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 44) < 512 * (2 * m) + 44 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 44 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_44] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 44) < 512 * (2 * m) + 44 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_44 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 44) < 512 * (2 * m + 1) + 44 := by
  apply refinement_cleared (k := 9) (r := 44) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_44]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 45). -/
theorem data_9_45 : oddCount 45 9 = 4 ∧
    acceleratedOrbit 9 45 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_45 : gap 9 45 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_45 : threshold 9 45 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_45 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 45) = 81 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 45
  rw [data_9_45.1, data_9_45.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_45 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 45) = 81 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 45
  rw [data_9_45.1, data_9_45.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_45 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 45) < 512 * (2 * m) + 45 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 45 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_45] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 45) < 512 * (2 * m) + 45 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_45 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 45) < 512 * (2 * m + 1) + 45 := by
  apply refinement_cleared (k := 9) (r := 45) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_45]; decide

end Collatz.Research.RefinementAtlas.Batch148
