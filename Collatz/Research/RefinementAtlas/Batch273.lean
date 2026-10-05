import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 273. -/
namespace Collatz.Research.RefinementAtlas.Batch273
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 38). -/
theorem data_10_38 : oddCount 38 10 = 5 ∧
    acceleratedOrbit 10 38 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_38 : gap 10 38 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_38 : threshold 10 38 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_38 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 38) = 243 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 38
  rw [data_10_38.1, data_10_38.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_38 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 38) = 243 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 38
  rw [data_10_38.1, data_10_38.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_38 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 38) < 1024 * (2 * m) + 38 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 38 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_38] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 38) < 1024 * (2 * m) + 38 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_38 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 38) < 1024 * (2 * m + 1) + 38 := by
  apply refinement_cleared (k := 10) (r := 38) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_38]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 39). -/
theorem data_10_39 : oddCount 39 10 = 6 ∧
    acceleratedOrbit 10 39 = 29 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_39 : gap 10 39 = 295 ∧ 729 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_39 : threshold 10 39 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_39 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 39) = 729 * (2 * m) + 29 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 39
  rw [data_10_39.1, data_10_39.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_39 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 39) = 729 * (2 * m + 1) + 29 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 39
  rw [data_10_39.1, data_10_39.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_39 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 39) < 1024 * (2 * m) + 39 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 39 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_39] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 39) < 1024 * (2 * m) + 39 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_39 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 39) < 1024 * (2 * m + 1) + 39 := by
  apply refinement_cleared (k := 10) (r := 39) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_39]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 40). -/
theorem data_10_40 : oddCount 40 10 = 3 ∧
    acceleratedOrbit 10 40 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_40 : gap 10 40 = 997 ∧ 27 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_40 : threshold 10 40 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_40 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 40) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 40
  rw [data_10_40.1, data_10_40.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_40 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 40) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 40
  rw [data_10_40.1, data_10_40.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_40 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 40) < 1024 * (2 * m) + 40 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 40 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_40] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 40) < 1024 * (2 * m) + 40 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_40 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 40) < 1024 * (2 * m + 1) + 40 := by
  apply refinement_cleared (k := 10) (r := 40) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_40]; decide

end Collatz.Research.RefinementAtlas.Batch273
