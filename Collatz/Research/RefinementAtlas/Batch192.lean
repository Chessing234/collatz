import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 192. -/
namespace Collatz.Research.RefinementAtlas.Batch192
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 218). -/
theorem data_9_218 : oddCount 218 9 = 5 ∧
    acceleratedOrbit 9 218 = 107 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_218 : gap 9 218 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_218 : threshold 9 218 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_218 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 218) = 243 * (2 * m) + 107 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 218
  rw [data_9_218.1, data_9_218.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_218 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 218) = 243 * (2 * m + 1) + 107 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 218
  rw [data_9_218.1, data_9_218.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_218 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 218) < 512 * (2 * m) + 218 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 218 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_218] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 218) < 512 * (2 * m) + 218 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_218 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 218) < 512 * (2 * m + 1) + 218 := by
  apply refinement_cleared (k := 9) (r := 218) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_218]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 220). -/
theorem data_9_220 : oddCount 220 9 = 5 ∧
    acceleratedOrbit 9 220 = 107 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_220 : gap 9 220 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_220 : threshold 9 220 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_220 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 220) = 243 * (2 * m) + 107 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 220
  rw [data_9_220.1, data_9_220.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_220 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 220) = 243 * (2 * m + 1) + 107 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 220
  rw [data_9_220.1, data_9_220.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_220 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 220) < 512 * (2 * m) + 220 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 220 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_220] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 220) < 512 * (2 * m) + 220 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_220 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 220) < 512 * (2 * m + 1) + 220 := by
  apply refinement_cleared (k := 9) (r := 220) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_220]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 221). -/
theorem data_9_221 : oddCount 221 9 = 5 ∧
    acceleratedOrbit 9 221 = 107 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_221 : gap 9 221 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_221 : threshold 9 221 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_221 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 221) = 243 * (2 * m) + 107 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 221
  rw [data_9_221.1, data_9_221.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_221 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 221) = 243 * (2 * m + 1) + 107 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 221
  rw [data_9_221.1, data_9_221.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_221 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 221) < 512 * (2 * m) + 221 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 221 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_221] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 221) < 512 * (2 * m) + 221 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_221 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 221) < 512 * (2 * m + 1) + 221 := by
  apply refinement_cleared (k := 9) (r := 221) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_221]; decide

end Collatz.Research.RefinementAtlas.Batch192
