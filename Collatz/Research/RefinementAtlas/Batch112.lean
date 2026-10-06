import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 112. -/
namespace Collatz.Research.RefinementAtlas.Batch112
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 171). -/
theorem data_8_171 : oddCount 171 8 = 5 ∧
    acceleratedOrbit 8 171 = 164 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_171 : gap 8 171 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_171 : threshold 8 171 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_171 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 171) = 243 * (2 * m) + 164 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 171
  rw [data_8_171.1, data_8_171.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_171 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 171) = 243 * (2 * m + 1) + 164 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 171
  rw [data_8_171.1, data_8_171.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_171 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 171) < 256 * (2 * m) + 171 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 171 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_171] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 171) < 256 * (2 * m) + 171 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_171 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 171) < 256 * (2 * m + 1) + 171 := by
  apply refinement_cleared (k := 8) (r := 171) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_171]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 172). -/
theorem data_8_172 : oddCount 172 8 = 4 ∧
    acceleratedOrbit 8 172 = 56 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_172 : gap 8 172 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_172 : threshold 8 172 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_172 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 172) = 81 * (2 * m) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 172
  rw [data_8_172.1, data_8_172.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_172 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 172) = 81 * (2 * m + 1) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 172
  rw [data_8_172.1, data_8_172.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_172 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 172) < 256 * (2 * m) + 172 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 172 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_172] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 172) < 256 * (2 * m) + 172 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_172 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 172) < 256 * (2 * m + 1) + 172 := by
  apply refinement_cleared (k := 8) (r := 172) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_172]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 173). -/
theorem data_8_173 : oddCount 173 8 = 4 ∧
    acceleratedOrbit 8 173 = 56 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_173 : gap 8 173 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_173 : threshold 8 173 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_173 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 173) = 81 * (2 * m) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 173
  rw [data_8_173.1, data_8_173.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_173 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 173) = 81 * (2 * m + 1) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 173
  rw [data_8_173.1, data_8_173.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_173 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 173) < 256 * (2 * m) + 173 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 173 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_173] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 173) < 256 * (2 * m) + 173 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_173 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 173) < 256 * (2 * m + 1) + 173 := by
  apply refinement_cleared (k := 8) (r := 173) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_173]; decide

end Collatz.Research.RefinementAtlas.Batch112
