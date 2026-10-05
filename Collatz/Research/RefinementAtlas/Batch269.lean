import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 269. -/
namespace Collatz.Research.RefinementAtlas.Batch269
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 24). -/
theorem data_10_24 : oddCount 24 10 = 3 ∧
    acceleratedOrbit 10 24 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_24 : gap 10 24 = 997 ∧ 27 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_24 : threshold 10 24 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_24 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 24) = 27 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 24
  rw [data_10_24.1, data_10_24.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_24 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 24) = 27 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 24
  rw [data_10_24.1, data_10_24.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_24 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 24) < 1024 * (2 * m) + 24 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 24 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_24] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 24) < 1024 * (2 * m) + 24 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_24 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 24) < 1024 * (2 * m + 1) + 24 := by
  apply refinement_cleared (k := 10) (r := 24) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_24]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 25). -/
theorem data_10_25 : oddCount 25 10 = 6 ∧
    acceleratedOrbit 10 25 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_25 : gap 10 25 = 295 ∧ 729 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_25 : threshold 10 25 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_25 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 25) = 729 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 25
  rw [data_10_25.1, data_10_25.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_25 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 25) = 729 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 25
  rw [data_10_25.1, data_10_25.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_25 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 25) < 1024 * (2 * m) + 25 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 25 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_25] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 25) < 1024 * (2 * m) + 25 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_25 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 25) < 1024 * (2 * m + 1) + 25 := by
  apply refinement_cleared (k := 10) (r := 25) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_25]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 26). -/
theorem data_10_26 : oddCount 26 10 = 3 ∧
    acceleratedOrbit 10 26 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_26 : gap 10 26 = 997 ∧ 27 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_26 : threshold 10 26 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_26 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 26) = 27 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 26
  rw [data_10_26.1, data_10_26.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_26 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 26) = 27 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 26
  rw [data_10_26.1, data_10_26.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_26 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 26) < 1024 * (2 * m) + 26 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 26 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_26] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 26) < 1024 * (2 * m) + 26 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_26 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 26) < 1024 * (2 * m + 1) + 26 := by
  apply refinement_cleared (k := 10) (r := 26) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_26]; decide

end Collatz.Research.RefinementAtlas.Batch269
