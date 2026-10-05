import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 281. -/
namespace Collatz.Research.RefinementAtlas.Batch281
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 68). -/
theorem data_10_68 : oddCount 68 10 = 3 ∧
    acceleratedOrbit 10 68 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_68 : gap 10 68 = 997 ∧ 27 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_68 : threshold 10 68 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_68 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 68) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 68
  rw [data_10_68.1, data_10_68.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_68 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 68) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 68
  rw [data_10_68.1, data_10_68.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_68 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 68) < 1024 * (2 * m) + 68 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 68 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_68] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 68) < 1024 * (2 * m) + 68 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_68 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 68) < 1024 * (2 * m + 1) + 68 := by
  apply refinement_cleared (k := 10) (r := 68) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_68]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 69). -/
theorem data_10_69 : oddCount 69 10 = 3 ∧
    acceleratedOrbit 10 69 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_69 : gap 10 69 = 997 ∧ 27 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_69 : threshold 10 69 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_69 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 69) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 69
  rw [data_10_69.1, data_10_69.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_69 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 69) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 69
  rw [data_10_69.1, data_10_69.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_69 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 69) < 1024 * (2 * m) + 69 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 69 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_69] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 69) < 1024 * (2 * m) + 69 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_69 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 69) < 1024 * (2 * m + 1) + 69 := by
  apply refinement_cleared (k := 10) (r := 69) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_69]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 70). -/
theorem data_10_70 : oddCount 70 10 = 3 ∧
    acceleratedOrbit 10 70 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_70 : gap 10 70 = 997 ∧ 27 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_70 : threshold 10 70 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_70 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 70) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 70
  rw [data_10_70.1, data_10_70.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_70 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 70) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 70
  rw [data_10_70.1, data_10_70.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_70 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 70) < 1024 * (2 * m) + 70 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 70 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_70] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 70) < 1024 * (2 * m) + 70 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_70 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 70) < 1024 * (2 * m + 1) + 70 := by
  apply refinement_cleared (k := 10) (r := 70) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_70]; decide

end Collatz.Research.RefinementAtlas.Batch281
