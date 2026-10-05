import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 100. -/
namespace Collatz.Research.RefinementAtlas.Batch100
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 130). -/
theorem data_8_130 : oddCount 130 8 = 3 ∧
    acceleratedOrbit 8 130 = 14 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_130 : gap 8 130 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_130 : threshold 8 130 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_130 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 130) = 27 * (2 * m) + 14 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 130
  rw [data_8_130.1, data_8_130.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_130 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 130) = 27 * (2 * m + 1) + 14 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 130
  rw [data_8_130.1, data_8_130.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_130 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 130) < 256 * (2 * m) + 130 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 130 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_130] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 130) < 256 * (2 * m) + 130 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_130 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 130) < 256 * (2 * m + 1) + 130 := by
  apply refinement_cleared (k := 8) (r := 130) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_130]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 131). -/
theorem data_8_131 : oddCount 131 8 = 3 ∧
    acceleratedOrbit 8 131 = 14 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_131 : gap 8 131 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_131 : threshold 8 131 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_131 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 131) = 27 * (2 * m) + 14 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 131
  rw [data_8_131.1, data_8_131.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_131 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 131) = 27 * (2 * m + 1) + 14 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 131
  rw [data_8_131.1, data_8_131.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_131 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 131) < 256 * (2 * m) + 131 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 131 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_131] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 131) < 256 * (2 * m) + 131 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_131 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 131) < 256 * (2 * m + 1) + 131 := by
  apply refinement_cleared (k := 8) (r := 131) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_131]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 132). -/
theorem data_8_132 : oddCount 132 8 = 4 ∧
    acceleratedOrbit 8 132 = 44 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_132 : gap 8 132 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_132 : threshold 8 132 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_132 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 132) = 81 * (2 * m) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 132
  rw [data_8_132.1, data_8_132.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_132 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 132) = 81 * (2 * m + 1) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 132
  rw [data_8_132.1, data_8_132.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_132 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 132) < 256 * (2 * m) + 132 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 132 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_132] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 132) < 256 * (2 * m) + 132 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_132 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 132) < 256 * (2 * m + 1) + 132 := by
  apply refinement_cleared (k := 8) (r := 132) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_132]; decide

end Collatz.Research.RefinementAtlas.Batch100
