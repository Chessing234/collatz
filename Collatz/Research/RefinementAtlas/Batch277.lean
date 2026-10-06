import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 277. -/
namespace Collatz.Research.RefinementAtlas.Batch277
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 52). -/
theorem data_10_52 : oddCount 52 10 = 3 ∧
    acceleratedOrbit 10 52 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_52 : gap 10 52 = 997 ∧ 27 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_52 : threshold 10 52 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_52 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 52) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 52
  rw [data_10_52.1, data_10_52.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_52 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 52) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 52
  rw [data_10_52.1, data_10_52.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_52 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 52) < 1024 * (2 * m) + 52 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 52 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_52] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 52) < 1024 * (2 * m) + 52 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_52 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 52) < 1024 * (2 * m + 1) + 52 := by
  apply refinement_cleared (k := 10) (r := 52) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_52]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 53). -/
theorem data_10_53 : oddCount 53 10 = 3 ∧
    acceleratedOrbit 10 53 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_53 : gap 10 53 = 997 ∧ 27 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_53 : threshold 10 53 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_53 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 53) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 53
  rw [data_10_53.1, data_10_53.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_53 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 53) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 53
  rw [data_10_53.1, data_10_53.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_53 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 53) < 1024 * (2 * m) + 53 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 53 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_53] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 53) < 1024 * (2 * m) + 53 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_53 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 53) < 1024 * (2 * m + 1) + 53 := by
  apply refinement_cleared (k := 10) (r := 53) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_53]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 56). -/
theorem data_10_56 : oddCount 56 10 = 4 ∧
    acceleratedOrbit 10 56 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_56 : gap 10 56 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_56 : threshold 10 56 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_56 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 56) = 81 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 56
  rw [data_10_56.1, data_10_56.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_56 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 56) = 81 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 56
  rw [data_10_56.1, data_10_56.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_56 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 56) < 1024 * (2 * m) + 56 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 56 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_56] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 56) < 1024 * (2 * m) + 56 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_56 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 56) < 1024 * (2 * m + 1) + 56 := by
  apply refinement_cleared (k := 10) (r := 56) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_56]; decide

end Collatz.Research.RefinementAtlas.Batch277
