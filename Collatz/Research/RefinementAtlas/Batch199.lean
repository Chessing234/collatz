import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 199. -/
namespace Collatz.Research.RefinementAtlas.Batch199
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 249). -/
theorem data_9_249 : oddCount 249 9 = 5 ∧
    acceleratedOrbit 9 249 = 119 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_249 : gap 9 249 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_249 : threshold 9 249 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_249 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 249) = 243 * (2 * m) + 119 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 249
  rw [data_9_249.1, data_9_249.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_249 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 249) = 243 * (2 * m + 1) + 119 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 249
  rw [data_9_249.1, data_9_249.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_249 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 249) < 512 * (2 * m) + 249 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 249 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_249] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 249) < 512 * (2 * m) + 249 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_249 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 249) < 512 * (2 * m + 1) + 249 := by
  apply refinement_cleared (k := 9) (r := 249) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_249]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 250). -/
theorem data_9_250 : oddCount 250 9 = 5 ∧
    acceleratedOrbit 9 250 = 121 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_250 : gap 9 250 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_250 : threshold 9 250 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_250 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 250) = 243 * (2 * m) + 121 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 250
  rw [data_9_250.1, data_9_250.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_250 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 250) = 243 * (2 * m + 1) + 121 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 250
  rw [data_9_250.1, data_9_250.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_250 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 250) < 512 * (2 * m) + 250 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 250 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_250] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 250) < 512 * (2 * m) + 250 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_250 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 250) < 512 * (2 * m + 1) + 250 := by
  apply refinement_cleared (k := 9) (r := 250) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_250]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 256). -/
theorem data_9_256 : oddCount 256 9 = 1 ∧
    acceleratedOrbit 9 256 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_256 : gap 9 256 = 509 ∧ 3 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_256 : threshold 9 256 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_256 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 256) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 256
  rw [data_9_256.1, data_9_256.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_256 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 256) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 256
  rw [data_9_256.1, data_9_256.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_256 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 256) < 512 * (2 * m) + 256 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 256 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_256] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 256) < 512 * (2 * m) + 256 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_256 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 256) < 512 * (2 * m + 1) + 256 := by
  apply refinement_cleared (k := 9) (r := 256) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_256]; decide

end Collatz.Research.RefinementAtlas.Batch199
