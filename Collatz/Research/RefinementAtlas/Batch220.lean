import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 220. -/
namespace Collatz.Research.RefinementAtlas.Batch220
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 333). -/
theorem data_9_333 : oddCount 333 9 = 5 ∧
    acceleratedOrbit 9 333 = 161 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_333 : gap 9 333 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_333 : threshold 9 333 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_333 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 333) = 243 * (2 * m) + 161 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 333
  rw [data_9_333.1, data_9_333.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_333 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 333) = 243 * (2 * m + 1) + 161 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 333
  rw [data_9_333.1, data_9_333.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_333 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 333) < 512 * (2 * m) + 333 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 333 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_333] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 333) < 512 * (2 * m) + 333 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_333 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 333) < 512 * (2 * m + 1) + 333 := by
  apply refinement_cleared (k := 9) (r := 333) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_333]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 336). -/
theorem data_9_336 : oddCount 336 9 = 1 ∧
    acceleratedOrbit 9 336 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_336 : gap 9 336 = 509 ∧ 3 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_336 : threshold 9 336 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_336 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 336) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 336
  rw [data_9_336.1, data_9_336.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_336 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 336) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 336
  rw [data_9_336.1, data_9_336.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_336 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 336) < 512 * (2 * m) + 336 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 336 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_336] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 336) < 512 * (2 * m) + 336 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_336 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 336) < 512 * (2 * m + 1) + 336 := by
  apply refinement_cleared (k := 9) (r := 336) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_336]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 340). -/
theorem data_9_340 : oddCount 340 9 = 1 ∧
    acceleratedOrbit 9 340 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_340 : gap 9 340 = 509 ∧ 3 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_340 : threshold 9 340 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_340 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 340) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 340
  rw [data_9_340.1, data_9_340.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_340 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 340) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 340
  rw [data_9_340.1, data_9_340.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_340 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 340) < 512 * (2 * m) + 340 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 340 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_340] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 340) < 512 * (2 * m) + 340 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_340 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 340) < 512 * (2 * m + 1) + 340 := by
  apply refinement_cleared (k := 9) (r := 340) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_340]; decide

end Collatz.Research.RefinementAtlas.Batch220
