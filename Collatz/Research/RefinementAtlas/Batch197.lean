import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 197. -/
namespace Collatz.Research.RefinementAtlas.Batch197
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 241). -/
theorem data_9_241 : oddCount 241 9 = 3 ∧
    acceleratedOrbit 9 241 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_241 : gap 9 241 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_241 : threshold 9 241 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_241 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 241) = 27 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 241
  rw [data_9_241.1, data_9_241.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_241 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 241) = 27 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 241
  rw [data_9_241.1, data_9_241.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_241 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 241) < 512 * (2 * m) + 241 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 241 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_241] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 241) < 512 * (2 * m) + 241 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_241 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 241) < 512 * (2 * m + 1) + 241 := by
  apply refinement_cleared (k := 9) (r := 241) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_241]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 244). -/
theorem data_9_244 : oddCount 244 9 = 4 ∧
    acceleratedOrbit 9 244 = 40 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_244 : gap 9 244 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_244 : threshold 9 244 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_244 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 244) = 81 * (2 * m) + 40 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 244
  rw [data_9_244.1, data_9_244.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_244 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 244) = 81 * (2 * m + 1) + 40 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 244
  rw [data_9_244.1, data_9_244.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_244 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 244) < 512 * (2 * m) + 244 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 244 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_244] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 244) < 512 * (2 * m) + 244 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_244 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 244) < 512 * (2 * m + 1) + 244 := by
  apply refinement_cleared (k := 9) (r := 244) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_244]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 245). -/
theorem data_9_245 : oddCount 245 9 = 4 ∧
    acceleratedOrbit 9 245 = 40 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_245 : gap 9 245 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_245 : threshold 9 245 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_245 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 245) = 81 * (2 * m) + 40 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 245
  rw [data_9_245.1, data_9_245.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_245 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 245) = 81 * (2 * m + 1) + 40 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 245
  rw [data_9_245.1, data_9_245.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_245 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 245) < 512 * (2 * m) + 245 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 245 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_245] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 245) < 512 * (2 * m) + 245 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_245 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 245) < 512 * (2 * m + 1) + 245 := by
  apply refinement_cleared (k := 9) (r := 245) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_245]; decide

end Collatz.Research.RefinementAtlas.Batch197
