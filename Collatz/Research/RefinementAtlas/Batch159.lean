import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 159. -/
namespace Collatz.Research.RefinementAtlas.Batch159
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 85). -/
theorem data_9_85 : oddCount 85 9 = 2 ∧
    acceleratedOrbit 9 85 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_85 : gap 9 85 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_85 : threshold 9 85 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_85 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 85) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 85
  rw [data_9_85.1, data_9_85.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_85 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 85) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 85
  rw [data_9_85.1, data_9_85.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_85 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 85) < 512 * (2 * m) + 85 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 85 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_85] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 85) < 512 * (2 * m) + 85 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_85 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 85) < 512 * (2 * m + 1) + 85 := by
  apply refinement_cleared (k := 9) (r := 85) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_85]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 86). -/
theorem data_9_86 : oddCount 86 9 = 4 ∧
    acceleratedOrbit 9 86 = 14 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_86 : gap 9 86 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_86 : threshold 9 86 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_86 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 86) = 81 * (2 * m) + 14 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 86
  rw [data_9_86.1, data_9_86.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_86 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 86) = 81 * (2 * m + 1) + 14 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 86
  rw [data_9_86.1, data_9_86.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_86 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 86) < 512 * (2 * m) + 86 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 86 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_86] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 86) < 512 * (2 * m) + 86 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_86 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 86) < 512 * (2 * m + 1) + 86 := by
  apply refinement_cleared (k := 9) (r := 86) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_86]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 87). -/
theorem data_9_87 : oddCount 87 9 = 4 ∧
    acceleratedOrbit 9 87 = 14 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_87 : gap 9 87 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_87 : threshold 9 87 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_87 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 87) = 81 * (2 * m) + 14 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 87
  rw [data_9_87.1, data_9_87.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_87 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 87) = 81 * (2 * m + 1) + 14 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 87
  rw [data_9_87.1, data_9_87.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_87 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 87) < 512 * (2 * m) + 87 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 87 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_87] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 87) < 512 * (2 * m) + 87 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_87 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 87) < 512 * (2 * m + 1) + 87 := by
  apply refinement_cleared (k := 9) (r := 87) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_87]; decide

end Collatz.Research.RefinementAtlas.Batch159
