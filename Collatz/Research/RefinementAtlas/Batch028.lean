import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 028. -/
namespace Collatz.Research.RefinementAtlas.Batch028
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (6, 38). -/
theorem data_6_38 : oddCount 38 6 = 3 ∧
    acceleratedOrbit 6 38 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_38 : gap 6 38 = 37 ∧ 27 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_38 : threshold 6 38 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_38 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 38) = 27 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 38
  rw [data_6_38.1, data_6_38.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_38 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 38) = 27 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 38
  rw [data_6_38.1, data_6_38.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_38 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 38) < 64 * (2 * m) + 38 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 38 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_38] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 38) < 64 * (2 * m) + 38 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_38 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 38) < 64 * (2 * m + 1) + 38 := by
  apply refinement_cleared (k := 6) (r := 38) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_38]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 40). -/
theorem data_6_40 : oddCount 40 6 = 1 ∧
    acceleratedOrbit 6 40 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_40 : gap 6 40 = 61 ∧ 3 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_40 : threshold 6 40 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_40 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 40) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 40
  rw [data_6_40.1, data_6_40.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_40 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 40) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 40
  rw [data_6_40.1, data_6_40.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_40 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 40) < 64 * (2 * m) + 40 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 40 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_40] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 40) < 64 * (2 * m) + 40 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_40 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 40) < 64 * (2 * m + 1) + 40 := by
  apply refinement_cleared (k := 6) (r := 40) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_40]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 42). -/
theorem data_6_42 : oddCount 42 6 = 1 ∧
    acceleratedOrbit 6 42 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_42 : gap 6 42 = 61 ∧ 3 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_42 : threshold 6 42 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_42 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 42) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 42
  rw [data_6_42.1, data_6_42.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_42 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 42) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 42
  rw [data_6_42.1, data_6_42.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_42 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 42) < 64 * (2 * m) + 42 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 42 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_42] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 42) < 64 * (2 * m) + 42 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_42 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 42) < 64 * (2 * m + 1) + 42 := by
  apply refinement_cleared (k := 6) (r := 42) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_42]; decide

end Collatz.Research.RefinementAtlas.Batch028
