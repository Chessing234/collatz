import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 274. -/
namespace Collatz.Research.RefinementAtlas.Batch274
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 42). -/
theorem data_10_42 : oddCount 42 10 = 3 ∧
    acceleratedOrbit 10 42 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_42 : gap 10 42 = 997 ∧ 27 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_42 : threshold 10 42 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_42 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 42) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 42
  rw [data_10_42.1, data_10_42.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_42 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 42) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 42
  rw [data_10_42.1, data_10_42.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_42 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 42) < 1024 * (2 * m) + 42 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 42 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_42] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 42) < 1024 * (2 * m) + 42 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_42 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 42) < 1024 * (2 * m + 1) + 42 := by
  apply refinement_cleared (k := 10) (r := 42) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_42]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 43). -/
theorem data_10_43 : oddCount 43 10 = 5 ∧
    acceleratedOrbit 10 43 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_43 : gap 10 43 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_43 : threshold 10 43 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_43 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 43) = 243 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 43
  rw [data_10_43.1, data_10_43.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_43 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 43) = 243 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 43
  rw [data_10_43.1, data_10_43.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_43 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 43) < 1024 * (2 * m) + 43 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 43 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_43] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 43) < 1024 * (2 * m) + 43 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_43 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 43) < 1024 * (2 * m + 1) + 43 := by
  apply refinement_cleared (k := 10) (r := 43) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_43]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 44). -/
theorem data_10_44 : oddCount 44 10 = 4 ∧
    acceleratedOrbit 10 44 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_44 : gap 10 44 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_44 : threshold 10 44 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_44 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 44) = 81 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 44
  rw [data_10_44.1, data_10_44.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_44 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 44) = 81 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 44
  rw [data_10_44.1, data_10_44.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_44 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 44) < 1024 * (2 * m) + 44 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 44 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_44] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 44) < 1024 * (2 * m) + 44 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_44 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 44) < 1024 * (2 * m + 1) + 44 := by
  apply refinement_cleared (k := 10) (r := 44) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_44]; decide

end Collatz.Research.RefinementAtlas.Batch274
