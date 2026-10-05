import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 177. -/
namespace Collatz.Research.RefinementAtlas.Batch177
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 160). -/
theorem data_9_160 : oddCount 160 9 = 1 ∧
    acceleratedOrbit 9 160 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_160 : gap 9 160 = 509 ∧ 3 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_160 : threshold 9 160 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_160 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 160) = 3 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 160
  rw [data_9_160.1, data_9_160.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_160 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 160) = 3 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 160
  rw [data_9_160.1, data_9_160.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_160 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 160) < 512 * (2 * m) + 160 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 160 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_160] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 160) < 512 * (2 * m) + 160 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_160 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 160) < 512 * (2 * m + 1) + 160 := by
  apply refinement_cleared (k := 9) (r := 160) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_160]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 162). -/
theorem data_9_162 : oddCount 162 9 = 5 ∧
    acceleratedOrbit 9 162 = 80 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_162 : gap 9 162 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_162 : threshold 9 162 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_162 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 162) = 243 * (2 * m) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 162
  rw [data_9_162.1, data_9_162.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_162 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 162) = 243 * (2 * m + 1) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 162
  rw [data_9_162.1, data_9_162.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_162 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 162) < 512 * (2 * m) + 162 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 162 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_162] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 162) < 512 * (2 * m) + 162 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_162 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 162) < 512 * (2 * m + 1) + 162 := by
  apply refinement_cleared (k := 9) (r := 162) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_162]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 163). -/
theorem data_9_163 : oddCount 163 9 = 5 ∧
    acceleratedOrbit 9 163 = 80 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_163 : gap 9 163 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_163 : threshold 9 163 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_163 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 163) = 243 * (2 * m) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 163
  rw [data_9_163.1, data_9_163.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_163 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 163) = 243 * (2 * m + 1) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 163
  rw [data_9_163.1, data_9_163.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_163 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 163) < 512 * (2 * m) + 163 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 163 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_163] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 163) < 512 * (2 * m) + 163 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_163 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 163) < 512 * (2 * m + 1) + 163 := by
  apply refinement_cleared (k := 9) (r := 163) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_163]; decide

end Collatz.Research.RefinementAtlas.Batch177
