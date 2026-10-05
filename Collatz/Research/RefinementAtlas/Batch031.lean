import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 031. -/
namespace Collatz.Research.RefinementAtlas.Batch031
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (6, 51). -/
theorem data_6_51 : oddCount 51 6 = 3 ∧
    acceleratedOrbit 6 51 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_51 : gap 6 51 = 37 ∧ 27 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_51 : threshold 6 51 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_51 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 51) = 27 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 51
  rw [data_6_51.1, data_6_51.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_51 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 51) = 27 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 51
  rw [data_6_51.1, data_6_51.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_51 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 51) < 64 * (2 * m) + 51 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 51 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_51] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 51) < 64 * (2 * m) + 51 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_51 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 51) < 64 * (2 * m + 1) + 51 := by
  apply refinement_cleared (k := 6) (r := 51) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_51]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 52). -/
theorem data_6_52 : oddCount 52 6 = 2 ∧
    acceleratedOrbit 6 52 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_52 : gap 6 52 = 55 ∧ 9 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_52 : threshold 6 52 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_52 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 52) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 52
  rw [data_6_52.1, data_6_52.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_52 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 52) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 52
  rw [data_6_52.1, data_6_52.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_52 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 52) < 64 * (2 * m) + 52 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 52 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_52] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 52) < 64 * (2 * m) + 52 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_52 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 52) < 64 * (2 * m + 1) + 52 := by
  apply refinement_cleared (k := 6) (r := 52) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_52]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 53). -/
theorem data_6_53 : oddCount 53 6 = 2 ∧
    acceleratedOrbit 6 53 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_53 : gap 6 53 = 55 ∧ 9 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_53 : threshold 6 53 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_53 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 53) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 53
  rw [data_6_53.1, data_6_53.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_53 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 53) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 53
  rw [data_6_53.1, data_6_53.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_53 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 53) < 64 * (2 * m) + 53 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 53 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_53] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 53) < 64 * (2 * m) + 53 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_53 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 53) < 64 * (2 * m + 1) + 53 := by
  apply refinement_cleared (k := 6) (r := 53) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_53]; decide

end Collatz.Research.RefinementAtlas.Batch031
