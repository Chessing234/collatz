import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 189. -/
namespace Collatz.Research.RefinementAtlas.Batch189
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 209). -/
theorem data_9_209 : oddCount 209 9 = 5 ∧
    acceleratedOrbit 9 209 = 101 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_209 : gap 9 209 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_209 : threshold 9 209 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_209 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 209) = 243 * (2 * m) + 101 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 209
  rw [data_9_209.1, data_9_209.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_209 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 209) = 243 * (2 * m + 1) + 101 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 209
  rw [data_9_209.1, data_9_209.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_209 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 209) < 512 * (2 * m) + 209 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 209 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_209] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 209) < 512 * (2 * m) + 209 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_209 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 209) < 512 * (2 * m + 1) + 209 := by
  apply refinement_cleared (k := 9) (r := 209) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_209]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 210). -/
theorem data_9_210 : oddCount 210 9 = 5 ∧
    acceleratedOrbit 9 210 = 101 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_210 : gap 9 210 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_210 : threshold 9 210 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_210 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 210) = 243 * (2 * m) + 101 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 210
  rw [data_9_210.1, data_9_210.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_210 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 210) = 243 * (2 * m + 1) + 101 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 210
  rw [data_9_210.1, data_9_210.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_210 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 210) < 512 * (2 * m) + 210 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 210 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_210] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 210) < 512 * (2 * m) + 210 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_210 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 210) < 512 * (2 * m + 1) + 210 := by
  apply refinement_cleared (k := 9) (r := 210) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_210]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 211). -/
theorem data_9_211 : oddCount 211 9 = 5 ∧
    acceleratedOrbit 9 211 = 101 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_211 : gap 9 211 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_211 : threshold 9 211 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_211 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 211) = 243 * (2 * m) + 101 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 211
  rw [data_9_211.1, data_9_211.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_211 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 211) = 243 * (2 * m + 1) + 101 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 211
  rw [data_9_211.1, data_9_211.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_211 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 211) < 512 * (2 * m) + 211 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 211 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_211] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 211) < 512 * (2 * m) + 211 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_211 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 211) < 512 * (2 * m + 1) + 211 := by
  apply refinement_cleared (k := 9) (r := 211) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_211]; decide

end Collatz.Research.RefinementAtlas.Batch189
