import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 179. -/
namespace Collatz.Research.RefinementAtlas.Batch179
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 172). -/
theorem data_9_172 : oddCount 172 9 = 4 ∧
    acceleratedOrbit 9 172 = 28 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_172 : gap 9 172 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_172 : threshold 9 172 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_172 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 172) = 81 * (2 * m) + 28 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 172
  rw [data_9_172.1, data_9_172.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_172 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 172) = 81 * (2 * m + 1) + 28 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 172
  rw [data_9_172.1, data_9_172.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_172 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 172) < 512 * (2 * m) + 172 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 172 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_172] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 172) < 512 * (2 * m) + 172 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_172 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 172) < 512 * (2 * m + 1) + 172 := by
  apply refinement_cleared (k := 9) (r := 172) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_172]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 173). -/
theorem data_9_173 : oddCount 173 9 = 4 ∧
    acceleratedOrbit 9 173 = 28 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_173 : gap 9 173 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_173 : threshold 9 173 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_173 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 173) = 81 * (2 * m) + 28 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 173
  rw [data_9_173.1, data_9_173.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_173 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 173) = 81 * (2 * m + 1) + 28 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 173
  rw [data_9_173.1, data_9_173.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_173 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 173) < 512 * (2 * m) + 173 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 173 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_173] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 173) < 512 * (2 * m) + 173 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_173 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 173) < 512 * (2 * m + 1) + 173 := by
  apply refinement_cleared (k := 9) (r := 173) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_173]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 174). -/
theorem data_9_174 : oddCount 174 9 = 4 ∧
    acceleratedOrbit 9 174 = 28 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_174 : gap 9 174 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_174 : threshold 9 174 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_174 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 174) = 81 * (2 * m) + 28 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 174
  rw [data_9_174.1, data_9_174.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_174 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 174) = 81 * (2 * m + 1) + 28 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 174
  rw [data_9_174.1, data_9_174.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_174 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 174) < 512 * (2 * m) + 174 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 174 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_174] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 174) < 512 * (2 * m) + 174 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_174 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 174) < 512 * (2 * m + 1) + 174 := by
  apply refinement_cleared (k := 9) (r := 174) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_174]; decide

end Collatz.Research.RefinementAtlas.Batch179
