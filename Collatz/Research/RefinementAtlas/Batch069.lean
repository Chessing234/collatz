import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 069. -/
namespace Collatz.Research.RefinementAtlas.Batch069
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 17). -/
theorem data_8_17 : oddCount 17 8 = 3 ∧
    acceleratedOrbit 8 17 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_17 : gap 8 17 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_17 : threshold 8 17 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_17 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 17) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 17
  rw [data_8_17.1, data_8_17.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_17 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 17) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 17
  rw [data_8_17.1, data_8_17.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_17 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 17) < 256 * (2 * m) + 17 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 17 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_17] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 17) < 256 * (2 * m) + 17 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_17 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 17) < 256 * (2 * m + 1) + 17 := by
  apply refinement_cleared (k := 8) (r := 17) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_17]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 20). -/
theorem data_8_20 : oddCount 20 8 = 2 ∧
    acceleratedOrbit 8 20 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_20 : gap 8 20 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_20 : threshold 8 20 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_20 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 20) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 20
  rw [data_8_20.1, data_8_20.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_20 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 20) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 20
  rw [data_8_20.1, data_8_20.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_20 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 20) < 256 * (2 * m) + 20 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 20 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_20] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 20) < 256 * (2 * m) + 20 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_20 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 20) < 256 * (2 * m + 1) + 20 := by
  apply refinement_cleared (k := 8) (r := 20) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_20]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 21). -/
theorem data_8_21 : oddCount 21 8 = 2 ∧
    acceleratedOrbit 8 21 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_21 : gap 8 21 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_21 : threshold 8 21 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_21 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 21) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 21
  rw [data_8_21.1, data_8_21.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_21 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 21) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 21
  rw [data_8_21.1, data_8_21.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_21 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 21) < 256 * (2 * m) + 21 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 21 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_21] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 21) < 256 * (2 * m) + 21 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_21 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 21) < 256 * (2 * m + 1) + 21 := by
  apply refinement_cleared (k := 8) (r := 21) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_21]; decide

end Collatz.Research.RefinementAtlas.Batch069
