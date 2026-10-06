import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 135. -/
namespace Collatz.Research.RefinementAtlas.Batch135
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 250). -/
theorem data_8_250 : oddCount 250 8 = 5 ∧
    acceleratedOrbit 8 250 = 242 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_250 : gap 8 250 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_250 : threshold 8 250 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_250 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 250) = 243 * (2 * m) + 242 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 250
  rw [data_8_250.1, data_8_250.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_250 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 250) = 243 * (2 * m + 1) + 242 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 250
  rw [data_8_250.1, data_8_250.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_250 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 250) < 256 * (2 * m) + 250 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 250 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_250] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 250) < 256 * (2 * m) + 250 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_250 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 250) < 256 * (2 * m + 1) + 250 := by
  apply refinement_cleared (k := 8) (r := 250) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_250]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 2). -/
theorem data_9_2 : oddCount 2 9 = 4 ∧
    acceleratedOrbit 9 2 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_2 : gap 9 2 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_2 : threshold 9 2 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_2 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 2) = 81 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 2
  rw [data_9_2.1, data_9_2.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_2 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 2) = 81 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 2
  rw [data_9_2.1, data_9_2.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_2 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 2) < 512 * (2 * m) + 2 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 2 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_2] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 2) < 512 * (2 * m) + 2 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_2 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 2) < 512 * (2 * m + 1) + 2 := by
  apply refinement_cleared (k := 9) (r := 2) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_2]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 3). -/
theorem data_9_3 : oddCount 3 9 = 4 ∧
    acceleratedOrbit 9 3 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_3 : gap 9 3 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_3 : threshold 9 3 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_3 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 3) = 81 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 3
  rw [data_9_3.1, data_9_3.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_3 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 3) = 81 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 3
  rw [data_9_3.1, data_9_3.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_3 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 3) < 512 * (2 * m) + 3 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 3 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_3] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 3) < 512 * (2 * m) + 3 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_3 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 3) < 512 * (2 * m + 1) + 3 := by
  apply refinement_cleared (k := 9) (r := 3) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_3]; decide

end Collatz.Research.RefinementAtlas.Batch135
