import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 182. -/
namespace Collatz.Research.RefinementAtlas.Batch182
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 184). -/
theorem data_9_184 : oddCount 184 9 = 3 ∧
    acceleratedOrbit 9 184 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_184 : gap 9 184 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_184 : threshold 9 184 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_184 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 184) = 27 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 184
  rw [data_9_184.1, data_9_184.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_184 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 184) = 27 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 184
  rw [data_9_184.1, data_9_184.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_184 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 184) < 512 * (2 * m) + 184 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 184 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_184] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 184) < 512 * (2 * m) + 184 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_184 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 184) < 512 * (2 * m + 1) + 184 := by
  apply refinement_cleared (k := 9) (r := 184) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_184]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 185). -/
theorem data_9_185 : oddCount 185 9 = 5 ∧
    acceleratedOrbit 9 185 = 89 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_185 : gap 9 185 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_185 : threshold 9 185 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_185 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 185) = 243 * (2 * m) + 89 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 185
  rw [data_9_185.1, data_9_185.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_185 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 185) = 243 * (2 * m + 1) + 89 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 185
  rw [data_9_185.1, data_9_185.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_185 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 185) < 512 * (2 * m) + 185 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 185 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_185] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 185) < 512 * (2 * m) + 185 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_185 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 185) < 512 * (2 * m + 1) + 185 := by
  apply refinement_cleared (k := 9) (r := 185) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_185]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 186). -/
theorem data_9_186 : oddCount 186 9 = 3 ∧
    acceleratedOrbit 9 186 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_186 : gap 9 186 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_186 : threshold 9 186 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_186 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 186) = 27 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 186
  rw [data_9_186.1, data_9_186.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_186 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 186) = 27 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 186
  rw [data_9_186.1, data_9_186.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_186 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 186) < 512 * (2 * m) + 186 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 186 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_186] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 186) < 512 * (2 * m) + 186 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_186 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 186) < 512 * (2 * m + 1) + 186 := by
  apply refinement_cleared (k := 9) (r := 186) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_186]; decide

end Collatz.Research.RefinementAtlas.Batch182
