import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 271. -/
namespace Collatz.Research.RefinementAtlas.Batch271
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 32). -/
theorem data_10_32 : oddCount 32 10 = 3 ∧
    acceleratedOrbit 10 32 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_32 : gap 10 32 = 997 ∧ 27 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_32 : threshold 10 32 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_32 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 32) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 32
  rw [data_10_32.1, data_10_32.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_32 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 32) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 32
  rw [data_10_32.1, data_10_32.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_32 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 32) < 1024 * (2 * m) + 32 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 32 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_32] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 32) < 1024 * (2 * m) + 32 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_32 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 32) < 1024 * (2 * m + 1) + 32 := by
  apply refinement_cleared (k := 10) (r := 32) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_32]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 33). -/
theorem data_10_33 : oddCount 33 10 = 6 ∧
    acceleratedOrbit 10 33 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_33 : gap 10 33 = 295 ∧ 729 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_33 : threshold 10 33 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_33 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 33) = 729 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 33
  rw [data_10_33.1, data_10_33.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_33 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 33) = 729 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 33
  rw [data_10_33.1, data_10_33.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_33 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 33) < 1024 * (2 * m) + 33 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 33 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_33] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 33) < 1024 * (2 * m) + 33 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_33 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 33) < 1024 * (2 * m + 1) + 33 := by
  apply refinement_cleared (k := 10) (r := 33) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_33]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 34). -/
theorem data_10_34 : oddCount 34 10 = 3 ∧
    acceleratedOrbit 10 34 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_34 : gap 10 34 = 997 ∧ 27 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_34 : threshold 10 34 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_34 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 34) = 27 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 34
  rw [data_10_34.1, data_10_34.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_34 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 34) = 27 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 34
  rw [data_10_34.1, data_10_34.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_34 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 34) < 1024 * (2 * m) + 34 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 34 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_34] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 34) < 1024 * (2 * m) + 34 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_34 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 34) < 1024 * (2 * m + 1) + 34 := by
  apply refinement_cleared (k := 10) (r := 34) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_34]; decide

end Collatz.Research.RefinementAtlas.Batch271
