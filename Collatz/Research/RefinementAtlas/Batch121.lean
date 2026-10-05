import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 121. -/
namespace Collatz.Research.RefinementAtlas.Batch121
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 199). -/
theorem data_8_199 : oddCount 199 8 = 5 ∧
    acceleratedOrbit 8 199 = 190 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_199 : gap 8 199 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_199 : threshold 8 199 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_199 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 199) = 243 * (2 * m) + 190 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 199
  rw [data_8_199.1, data_8_199.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_199 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 199) = 243 * (2 * m + 1) + 190 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 199
  rw [data_8_199.1, data_8_199.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_199 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 199) < 256 * (2 * m) + 199 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 199 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_199] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 199) < 256 * (2 * m) + 199 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_199 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 199) < 256 * (2 * m + 1) + 199 := by
  apply refinement_cleared (k := 8) (r := 199) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_199]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 200). -/
theorem data_8_200 : oddCount 200 8 = 3 ∧
    acceleratedOrbit 8 200 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_200 : gap 8 200 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_200 : threshold 8 200 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_200 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 200) = 27 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 200
  rw [data_8_200.1, data_8_200.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_200 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 200) = 27 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 200
  rw [data_8_200.1, data_8_200.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_200 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 200) < 256 * (2 * m) + 200 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 200 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_200] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 200) < 256 * (2 * m) + 200 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_200 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 200) < 256 * (2 * m + 1) + 200 := by
  apply refinement_cleared (k := 8) (r := 200) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_200]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 201). -/
theorem data_8_201 : oddCount 201 8 = 4 ∧
    acceleratedOrbit 8 201 = 64 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_201 : gap 8 201 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_201 : threshold 8 201 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_201 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 201) = 81 * (2 * m) + 64 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 201
  rw [data_8_201.1, data_8_201.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_201 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 201) = 81 * (2 * m + 1) + 64 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 201
  rw [data_8_201.1, data_8_201.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_201 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 201) < 256 * (2 * m) + 201 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 201 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_201] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 201) < 256 * (2 * m) + 201 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_201 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 201) < 256 * (2 * m + 1) + 201 := by
  apply refinement_cleared (k := 8) (r := 201) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_201]; decide

end Collatz.Research.RefinementAtlas.Batch121
