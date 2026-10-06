import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 099. -/
namespace Collatz.Research.RefinementAtlas.Batch099
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 125). -/
theorem data_8_125 : oddCount 125 8 = 5 ∧
    acceleratedOrbit 8 125 = 121 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_125 : gap 8 125 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_125 : threshold 8 125 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_125 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 125) = 243 * (2 * m) + 121 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 125
  rw [data_8_125.1, data_8_125.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_125 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 125) = 243 * (2 * m + 1) + 121 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 125
  rw [data_8_125.1, data_8_125.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_125 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 125) < 256 * (2 * m) + 125 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 125 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_125] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 125) < 256 * (2 * m) + 125 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_125 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 125) < 256 * (2 * m + 1) + 125 := by
  apply refinement_cleared (k := 8) (r := 125) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_125]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 128). -/
theorem data_8_128 : oddCount 128 8 = 1 ∧
    acceleratedOrbit 8 128 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_128 : gap 8 128 = 253 ∧ 3 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_128 : threshold 8 128 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_128 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 128) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 128
  rw [data_8_128.1, data_8_128.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_128 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 128) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 128
  rw [data_8_128.1, data_8_128.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_128 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 128) < 256 * (2 * m) + 128 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 128 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_128] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 128) < 256 * (2 * m) + 128 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_128 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 128) < 256 * (2 * m + 1) + 128 := by
  apply refinement_cleared (k := 8) (r := 128) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_128]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 129). -/
theorem data_8_129 : oddCount 129 8 = 5 ∧
    acceleratedOrbit 8 129 = 125 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_129 : gap 8 129 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_129 : threshold 8 129 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_129 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 129) = 243 * (2 * m) + 125 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 129
  rw [data_8_129.1, data_8_129.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_129 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 129) = 243 * (2 * m + 1) + 125 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 129
  rw [data_8_129.1, data_8_129.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_129 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 129) < 256 * (2 * m) + 129 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 129 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_129] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 129) < 256 * (2 * m) + 129 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_129 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 129) < 256 * (2 * m + 1) + 129 := by
  apply refinement_cleared (k := 8) (r := 129) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_129]; decide

end Collatz.Research.RefinementAtlas.Batch099
