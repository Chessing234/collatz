import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 279. -/
namespace Collatz.Research.RefinementAtlas.Batch279
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 60). -/
theorem data_10_60 : oddCount 60 10 = 4 ∧
    acceleratedOrbit 10 60 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_60 : gap 10 60 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_60 : threshold 10 60 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_60 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 60) = 81 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 60
  rw [data_10_60.1, data_10_60.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_60 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 60) = 81 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 60
  rw [data_10_60.1, data_10_60.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_60 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 60) < 1024 * (2 * m) + 60 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 60 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_60] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 60) < 1024 * (2 * m) + 60 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_60 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 60) < 1024 * (2 * m + 1) + 60 := by
  apply refinement_cleared (k := 10) (r := 60) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_60]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 61). -/
theorem data_10_61 : oddCount 61 10 = 4 ∧
    acceleratedOrbit 10 61 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_61 : gap 10 61 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_61 : threshold 10 61 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_61 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 61) = 81 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 61
  rw [data_10_61.1, data_10_61.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_61 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 61) = 81 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 61
  rw [data_10_61.1, data_10_61.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_61 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 61) < 1024 * (2 * m) + 61 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 61 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_61] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 61) < 1024 * (2 * m) + 61 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_61 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 61) < 1024 * (2 * m + 1) + 61 := by
  apply refinement_cleared (k := 10) (r := 61) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_61]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 64). -/
theorem data_10_64 : oddCount 64 10 = 2 ∧
    acceleratedOrbit 10 64 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_64 : gap 10 64 = 1015 ∧ 9 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_64 : threshold 10 64 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_64 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 64) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 64
  rw [data_10_64.1, data_10_64.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_64 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 64) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 64
  rw [data_10_64.1, data_10_64.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_64 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 64) < 1024 * (2 * m) + 64 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 64 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_64] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 64) < 1024 * (2 * m) + 64 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_64 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 64) < 1024 * (2 * m + 1) + 64 := by
  apply refinement_cleared (k := 10) (r := 64) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_64]; decide

end Collatz.Research.RefinementAtlas.Batch279
