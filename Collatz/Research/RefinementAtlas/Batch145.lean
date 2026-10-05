import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 145. -/
namespace Collatz.Research.RefinementAtlas.Batch145
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 33). -/
theorem data_9_33 : oddCount 33 9 = 5 ∧
    acceleratedOrbit 9 33 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_33 : gap 9 33 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_33 : threshold 9 33 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_33 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 33) = 243 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 33
  rw [data_9_33.1, data_9_33.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_33 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 33) = 243 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 33
  rw [data_9_33.1, data_9_33.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_33 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 33) < 512 * (2 * m) + 33 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 33 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_33] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 33) < 512 * (2 * m) + 33 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_33 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 33) < 512 * (2 * m + 1) + 33 := by
  apply refinement_cleared (k := 9) (r := 33) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_33]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 34). -/
theorem data_9_34 : oddCount 34 9 = 3 ∧
    acceleratedOrbit 9 34 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_34 : gap 9 34 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_34 : threshold 9 34 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_34 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 34) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 34
  rw [data_9_34.1, data_9_34.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_34 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 34) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 34
  rw [data_9_34.1, data_9_34.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_34 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 34) < 512 * (2 * m) + 34 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 34 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_34] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 34) < 512 * (2 * m) + 34 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_34 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 34) < 512 * (2 * m + 1) + 34 := by
  apply refinement_cleared (k := 9) (r := 34) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_34]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 35). -/
theorem data_9_35 : oddCount 35 9 = 3 ∧
    acceleratedOrbit 9 35 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_35 : gap 9 35 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_35 : threshold 9 35 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_35 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 35) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 35
  rw [data_9_35.1, data_9_35.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_35 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 35) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 35
  rw [data_9_35.1, data_9_35.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_35 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 35) < 512 * (2 * m) + 35 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 35 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_35] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 35) < 512 * (2 * m) + 35 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_35 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 35) < 512 * (2 * m + 1) + 35 := by
  apply refinement_cleared (k := 9) (r := 35) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_35]; decide

end Collatz.Research.RefinementAtlas.Batch145
