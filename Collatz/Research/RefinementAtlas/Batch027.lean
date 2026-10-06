import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 027. -/
namespace Collatz.Research.RefinementAtlas.Batch027
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (6, 35). -/
theorem data_6_35 : oddCount 35 6 = 2 ∧
    acceleratedOrbit 6 35 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_35 : gap 6 35 = 55 ∧ 9 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_35 : threshold 6 35 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_35 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 35) = 9 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 35
  rw [data_6_35.1, data_6_35.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_35 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 35) = 9 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 35
  rw [data_6_35.1, data_6_35.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_35 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 35) < 64 * (2 * m) + 35 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 35 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_35] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 35) < 64 * (2 * m) + 35 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_35 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 35) < 64 * (2 * m + 1) + 35 := by
  apply refinement_cleared (k := 6) (r := 35) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_35]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 36). -/
theorem data_6_36 : oddCount 36 6 = 3 ∧
    acceleratedOrbit 6 36 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_36 : gap 6 36 = 37 ∧ 27 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_36 : threshold 6 36 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_36 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 36) = 27 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 36
  rw [data_6_36.1, data_6_36.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_36 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 36) = 27 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 36
  rw [data_6_36.1, data_6_36.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_36 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 36) < 64 * (2 * m) + 36 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 36 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_36] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 36) < 64 * (2 * m) + 36 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_36 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 36) < 64 * (2 * m + 1) + 36 := by
  apply refinement_cleared (k := 6) (r := 36) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_36]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 37). -/
theorem data_6_37 : oddCount 37 6 = 3 ∧
    acceleratedOrbit 6 37 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_37 : gap 6 37 = 37 ∧ 27 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_37 : threshold 6 37 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_37 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 37) = 27 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 37
  rw [data_6_37.1, data_6_37.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_37 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 37) = 27 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 37
  rw [data_6_37.1, data_6_37.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_37 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 37) < 64 * (2 * m) + 37 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 37 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_37] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 37) < 64 * (2 * m) + 37 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_37 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 37) < 64 * (2 * m + 1) + 37 := by
  apply refinement_cleared (k := 6) (r := 37) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_37]; decide

end Collatz.Research.RefinementAtlas.Batch027
