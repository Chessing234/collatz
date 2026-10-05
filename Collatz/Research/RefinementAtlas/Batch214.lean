import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 214. -/
namespace Collatz.Research.RefinementAtlas.Batch214
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 309). -/
theorem data_9_309 : oddCount 309 9 = 3 ∧
    acceleratedOrbit 9 309 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_309 : gap 9 309 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_309 : threshold 9 309 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_309 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 309) = 27 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 309
  rw [data_9_309.1, data_9_309.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_309 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 309) = 27 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 309
  rw [data_9_309.1, data_9_309.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_309 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 309) < 512 * (2 * m) + 309 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 309 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_309] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 309) < 512 * (2 * m) + 309 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_309 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 309) < 512 * (2 * m + 1) + 309 := by
  apply refinement_cleared (k := 9) (r := 309) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_309]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 312). -/
theorem data_9_312 : oddCount 312 9 = 5 ∧
    acceleratedOrbit 9 312 = 152 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_312 : gap 9 312 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_312 : threshold 9 312 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_312 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 312) = 243 * (2 * m) + 152 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 312
  rw [data_9_312.1, data_9_312.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_312 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 312) = 243 * (2 * m + 1) + 152 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 312
  rw [data_9_312.1, data_9_312.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_312 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 312) < 512 * (2 * m) + 312 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 312 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_312] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 312) < 512 * (2 * m) + 312 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_312 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 312) < 512 * (2 * m + 1) + 312 := by
  apply refinement_cleared (k := 9) (r := 312) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_312]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 314). -/
theorem data_9_314 : oddCount 314 9 = 5 ∧
    acceleratedOrbit 9 314 = 152 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_314 : gap 9 314 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_314 : threshold 9 314 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_314 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 314) = 243 * (2 * m) + 152 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 314
  rw [data_9_314.1, data_9_314.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_314 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 314) = 243 * (2 * m + 1) + 152 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 314
  rw [data_9_314.1, data_9_314.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_314 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 314) < 512 * (2 * m) + 314 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 314 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_314] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 314) < 512 * (2 * m) + 314 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_314 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 314) < 512 * (2 * m + 1) + 314 := by
  apply refinement_cleared (k := 9) (r := 314) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_314]; decide

end Collatz.Research.RefinementAtlas.Batch214
