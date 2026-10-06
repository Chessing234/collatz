import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 172. -/
namespace Collatz.Research.RefinementAtlas.Batch172
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 141). -/
theorem data_9_141 : oddCount 141 9 = 3 ∧
    acceleratedOrbit 9 141 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_141 : gap 9 141 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_141 : threshold 9 141 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_141 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 141) = 27 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 141
  rw [data_9_141.1, data_9_141.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_141 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 141) = 27 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 141
  rw [data_9_141.1, data_9_141.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_141 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 141) < 512 * (2 * m) + 141 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 141 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_141] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 141) < 512 * (2 * m) + 141 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_141 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 141) < 512 * (2 * m + 1) + 141 := by
  apply refinement_cleared (k := 9) (r := 141) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_141]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 144). -/
theorem data_9_144 : oddCount 144 9 = 4 ∧
    acceleratedOrbit 9 144 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_144 : gap 9 144 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_144 : threshold 9 144 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_144 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 144) = 81 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 144
  rw [data_9_144.1, data_9_144.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_144 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 144) = 81 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 144
  rw [data_9_144.1, data_9_144.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_144 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 144) < 512 * (2 * m) + 144 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 144 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_144] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 144) < 512 * (2 * m) + 144 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_144 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 144) < 512 * (2 * m + 1) + 144 := by
  apply refinement_cleared (k := 9) (r := 144) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_144]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 145). -/
theorem data_9_145 : oddCount 145 9 = 5 ∧
    acceleratedOrbit 9 145 = 71 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_145 : gap 9 145 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_145 : threshold 9 145 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_145 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 145) = 243 * (2 * m) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 145
  rw [data_9_145.1, data_9_145.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_145 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 145) = 243 * (2 * m + 1) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 145
  rw [data_9_145.1, data_9_145.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_145 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 145) < 512 * (2 * m) + 145 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 145 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_145] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 145) < 512 * (2 * m) + 145 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_145 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 145) < 512 * (2 * m + 1) + 145 := by
  apply refinement_cleared (k := 9) (r := 145) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_145]; decide

end Collatz.Research.RefinementAtlas.Batch172
