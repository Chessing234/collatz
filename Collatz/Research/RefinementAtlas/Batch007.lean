import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 007. -/
namespace Collatz.Research.RefinementAtlas.Batch007
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (11, 1). -/
theorem data_11_1 : oddCount 1 11 = 6 ∧
    acceleratedOrbit 11 1 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_11_1 : gap 11 1 = 1319 ∧ 729 < 2048 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_11_1 : threshold 11 1 = 1 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_11_1 (m : Nat) :
    acceleratedOrbit 11 (2048 * (2 * m) + 1) = 729 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 11 (2 * m) 1
  rw [data_11_1.1, data_11_1.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_11_1 (m : Nat) :
    acceleratedOrbit 11 (2048 * (2 * m + 1) + 1) = 729 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 11 (2 * m + 1) 1
  rw [data_11_1.1, data_11_1.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_11_1 (m : Nat) :
    acceleratedOrbit 11 (2048 * (2 * m) + 1) < 2048 * (2 * m) + 1 ↔ 1 ≤ m := by
  have hc : 3 ^ oddCount 1 11 < 2 ^ 11 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_11_1] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 11 (2048 * (2 * m) + 1) < 2048 * (2 * m) + 1 ↔ 1 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_11_1 (m : Nat) :
    acceleratedOrbit 11 (2048 * (2 * m + 1) + 1) < 2048 * (2 * m + 1) + 1 := by
  apply refinement_cleared (k := 11) (r := 1) (s := 2) (q := 1)
  · decide
  · rw [cutoff_11_1]; decide

/-- Kernel-evaluated parity count and endpoint for (12, 1). -/
theorem data_12_1 : oddCount 1 12 = 6 ∧
    acceleratedOrbit 12 1 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_12_1 : gap 12 1 = 3367 ∧ 729 < 4096 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_12_1 : threshold 12 1 = 1 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_12_1 (m : Nat) :
    acceleratedOrbit 12 (4096 * (2 * m) + 1) = 729 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 (2 * m) 1
  rw [data_12_1.1, data_12_1.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_12_1 (m : Nat) :
    acceleratedOrbit 12 (4096 * (2 * m + 1) + 1) = 729 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 (2 * m + 1) 1
  rw [data_12_1.1, data_12_1.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_12_1 (m : Nat) :
    acceleratedOrbit 12 (4096 * (2 * m) + 1) < 4096 * (2 * m) + 1 ↔ 1 ≤ m := by
  have hc : 3 ^ oddCount 1 12 < 2 ^ 12 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_12_1] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 12 (4096 * (2 * m) + 1) < 4096 * (2 * m) + 1 ↔ 1 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_12_1 (m : Nat) :
    acceleratedOrbit 12 (4096 * (2 * m + 1) + 1) < 4096 * (2 * m + 1) + 1 := by
  apply refinement_cleared (k := 12) (r := 1) (s := 2) (q := 1)
  · decide
  · rw [cutoff_12_1]; decide

/-- Kernel-evaluated parity count and endpoint for (12, 2). -/
theorem data_12_2 : oddCount 2 12 = 6 ∧
    acceleratedOrbit 12 2 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_12_2 : gap 12 2 = 3367 ∧ 729 < 4096 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_12_2 : threshold 12 2 = 1 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_12_2 (m : Nat) :
    acceleratedOrbit 12 (4096 * (2 * m) + 2) = 729 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 (2 * m) 2
  rw [data_12_2.1, data_12_2.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_12_2 (m : Nat) :
    acceleratedOrbit 12 (4096 * (2 * m + 1) + 2) = 729 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 (2 * m + 1) 2
  rw [data_12_2.1, data_12_2.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_12_2 (m : Nat) :
    acceleratedOrbit 12 (4096 * (2 * m) + 2) < 4096 * (2 * m) + 2 ↔ 1 ≤ m := by
  have hc : 3 ^ oddCount 2 12 < 2 ^ 12 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_12_2] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 12 (4096 * (2 * m) + 2) < 4096 * (2 * m) + 2 ↔ 1 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_12_2 (m : Nat) :
    acceleratedOrbit 12 (4096 * (2 * m + 1) + 2) < 4096 * (2 * m + 1) + 2 := by
  apply refinement_cleared (k := 12) (r := 2) (s := 2) (q := 1)
  · decide
  · rw [cutoff_12_2]; decide

end Collatz.Research.RefinementAtlas.Batch007
