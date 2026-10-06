import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 104. -/
namespace Collatz.Research.RefinementAtlas.Batch104
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 143). -/
theorem data_8_143 : oddCount 143 8 = 5 ∧
    acceleratedOrbit 8 143 = 137 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_143 : gap 8 143 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_143 : threshold 8 143 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_143 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 143) = 243 * (2 * m) + 137 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 143
  rw [data_8_143.1, data_8_143.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_143 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 143) = 243 * (2 * m + 1) + 137 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 143
  rw [data_8_143.1, data_8_143.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_143 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 143) < 256 * (2 * m) + 143 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 143 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_143] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 143) < 256 * (2 * m) + 143 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_143 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 143) < 256 * (2 * m + 1) + 143 := by
  apply refinement_cleared (k := 8) (r := 143) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_143]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 144). -/
theorem data_8_144 : oddCount 144 8 = 3 ∧
    acceleratedOrbit 8 144 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_144 : gap 8 144 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_144 : threshold 8 144 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_144 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 144) = 27 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 144
  rw [data_8_144.1, data_8_144.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_144 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 144) = 27 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 144
  rw [data_8_144.1, data_8_144.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_144 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 144) < 256 * (2 * m) + 144 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 144 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_144] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 144) < 256 * (2 * m) + 144 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_144 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 144) < 256 * (2 * m + 1) + 144 := by
  apply refinement_cleared (k := 8) (r := 144) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_144]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 145). -/
theorem data_8_145 : oddCount 145 8 = 4 ∧
    acceleratedOrbit 8 145 = 47 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_145 : gap 8 145 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_145 : threshold 8 145 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_145 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 145) = 81 * (2 * m) + 47 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 145
  rw [data_8_145.1, data_8_145.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_145 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 145) = 81 * (2 * m + 1) + 47 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 145
  rw [data_8_145.1, data_8_145.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_145 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 145) < 256 * (2 * m) + 145 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 145 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_145] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 145) < 256 * (2 * m) + 145 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_145 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 145) < 256 * (2 * m + 1) + 145 := by
  apply refinement_cleared (k := 8) (r := 145) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_145]; decide

end Collatz.Research.RefinementAtlas.Batch104
