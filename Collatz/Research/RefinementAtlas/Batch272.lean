import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 272. -/
namespace Collatz.Research.RefinementAtlas.Batch272
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 35). -/
theorem data_10_35 : oddCount 35 10 = 3 ∧
    acceleratedOrbit 10 35 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_35 : gap 10 35 = 997 ∧ 27 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_35 : threshold 10 35 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_35 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 35) = 27 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 35
  rw [data_10_35.1, data_10_35.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_35 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 35) = 27 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 35
  rw [data_10_35.1, data_10_35.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_35 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 35) < 1024 * (2 * m) + 35 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 35 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_35] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 35) < 1024 * (2 * m) + 35 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_35 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 35) < 1024 * (2 * m + 1) + 35 := by
  apply refinement_cleared (k := 10) (r := 35) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_35]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 36). -/
theorem data_10_36 : oddCount 36 10 = 5 ∧
    acceleratedOrbit 10 36 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_36 : gap 10 36 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_36 : threshold 10 36 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_36 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 36) = 243 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 36
  rw [data_10_36.1, data_10_36.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_36 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 36) = 243 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 36
  rw [data_10_36.1, data_10_36.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_36 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 36) < 1024 * (2 * m) + 36 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 36 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_36] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 36) < 1024 * (2 * m) + 36 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_36 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 36) < 1024 * (2 * m + 1) + 36 := by
  apply refinement_cleared (k := 10) (r := 36) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_36]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 37). -/
theorem data_10_37 : oddCount 37 10 = 5 ∧
    acceleratedOrbit 10 37 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_37 : gap 10 37 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_37 : threshold 10 37 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_37 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 37) = 243 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 37
  rw [data_10_37.1, data_10_37.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_37 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 37) = 243 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 37
  rw [data_10_37.1, data_10_37.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_37 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 37) < 1024 * (2 * m) + 37 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 37 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_37] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 37) < 1024 * (2 * m) + 37 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_37 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 37) < 1024 * (2 * m + 1) + 37 := by
  apply refinement_cleared (k := 10) (r := 37) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_37]; decide

end Collatz.Research.RefinementAtlas.Batch272
