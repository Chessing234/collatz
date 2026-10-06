import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 116. -/
namespace Collatz.Research.RefinementAtlas.Batch116
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 183). -/
theorem data_8_183 : oddCount 183 8 = 5 ∧
    acceleratedOrbit 8 183 = 175 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_183 : gap 8 183 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_183 : threshold 8 183 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_183 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 183) = 243 * (2 * m) + 175 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 183
  rw [data_8_183.1, data_8_183.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_183 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 183) = 243 * (2 * m + 1) + 175 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 183
  rw [data_8_183.1, data_8_183.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_183 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 183) < 256 * (2 * m) + 183 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 183 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_183] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 183) < 256 * (2 * m) + 183 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_183 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 183) < 256 * (2 * m + 1) + 183 := by
  apply refinement_cleared (k := 8) (r := 183) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_183]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 184). -/
theorem data_8_184 : oddCount 184 8 = 3 ∧
    acceleratedOrbit 8 184 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_184 : gap 8 184 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_184 : threshold 8 184 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_184 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 184) = 27 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 184
  rw [data_8_184.1, data_8_184.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_184 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 184) = 27 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 184
  rw [data_8_184.1, data_8_184.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_184 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 184) < 256 * (2 * m) + 184 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 184 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_184] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 184) < 256 * (2 * m) + 184 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_184 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 184) < 256 * (2 * m + 1) + 184 := by
  apply refinement_cleared (k := 8) (r := 184) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_184]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 185). -/
theorem data_8_185 : oddCount 185 8 = 4 ∧
    acceleratedOrbit 8 185 = 59 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_185 : gap 8 185 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_185 : threshold 8 185 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_185 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 185) = 81 * (2 * m) + 59 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 185
  rw [data_8_185.1, data_8_185.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_185 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 185) = 81 * (2 * m + 1) + 59 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 185
  rw [data_8_185.1, data_8_185.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_185 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 185) < 256 * (2 * m) + 185 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 185 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_185] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 185) < 256 * (2 * m) + 185 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_185 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 185) < 256 * (2 * m + 1) + 185 := by
  apply refinement_cleared (k := 8) (r := 185) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_185]; decide

end Collatz.Research.RefinementAtlas.Batch116
