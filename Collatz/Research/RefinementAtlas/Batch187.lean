import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 187. -/
namespace Collatz.Research.RefinementAtlas.Batch187
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 201). -/
theorem data_9_201 : oddCount 201 9 = 4 ∧
    acceleratedOrbit 9 201 = 32 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_201 : gap 9 201 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_201 : threshold 9 201 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_201 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 201) = 81 * (2 * m) + 32 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 201
  rw [data_9_201.1, data_9_201.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_201 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 201) = 81 * (2 * m + 1) + 32 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 201
  rw [data_9_201.1, data_9_201.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_201 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 201) < 512 * (2 * m) + 201 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 201 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_201] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 201) < 512 * (2 * m) + 201 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_201 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 201) < 512 * (2 * m + 1) + 201 := by
  apply refinement_cleared (k := 9) (r := 201) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_201]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 202). -/
theorem data_9_202 : oddCount 202 9 = 3 ∧
    acceleratedOrbit 9 202 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_202 : gap 9 202 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_202 : threshold 9 202 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_202 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 202) = 27 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 202
  rw [data_9_202.1, data_9_202.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_202 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 202) = 27 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 202
  rw [data_9_202.1, data_9_202.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_202 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 202) < 512 * (2 * m) + 202 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 202 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_202] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 202) < 512 * (2 * m) + 202 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_202 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 202) < 512 * (2 * m + 1) + 202 := by
  apply refinement_cleared (k := 9) (r := 202) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_202]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 203). -/
theorem data_9_203 : oddCount 203 9 = 5 ∧
    acceleratedOrbit 9 203 = 98 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_203 : gap 9 203 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_203 : threshold 9 203 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_203 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 203) = 243 * (2 * m) + 98 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 203
  rw [data_9_203.1, data_9_203.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_203 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 203) = 243 * (2 * m + 1) + 98 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 203
  rw [data_9_203.1, data_9_203.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_203 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 203) < 512 * (2 * m) + 203 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 203 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_203] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 203) < 512 * (2 * m) + 203 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_203 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 203) < 512 * (2 * m + 1) + 203 := by
  apply refinement_cleared (k := 9) (r := 203) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_203]; decide

end Collatz.Research.RefinementAtlas.Batch187
