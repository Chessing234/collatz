import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 190. -/
namespace Collatz.Research.RefinementAtlas.Batch190
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 212). -/
theorem data_9_212 : oddCount 212 9 = 2 ∧
    acceleratedOrbit 9 212 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_212 : gap 9 212 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_212 : threshold 9 212 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_212 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 212) = 9 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 212
  rw [data_9_212.1, data_9_212.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_212 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 212) = 9 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 212
  rw [data_9_212.1, data_9_212.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_212 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 212) < 512 * (2 * m) + 212 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 212 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_212] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 212) < 512 * (2 * m) + 212 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_212 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 212) < 512 * (2 * m + 1) + 212 := by
  apply refinement_cleared (k := 9) (r := 212) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_212]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 213). -/
theorem data_9_213 : oddCount 213 9 = 2 ∧
    acceleratedOrbit 9 213 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_213 : gap 9 213 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_213 : threshold 9 213 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_213 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 213) = 9 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 213
  rw [data_9_213.1, data_9_213.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_213 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 213) = 9 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 213
  rw [data_9_213.1, data_9_213.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_213 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 213) < 512 * (2 * m) + 213 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 213 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_213] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 213) < 512 * (2 * m) + 213 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_213 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 213) < 512 * (2 * m + 1) + 213 := by
  apply refinement_cleared (k := 9) (r := 213) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_213]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 214). -/
theorem data_9_214 : oddCount 214 9 = 5 ∧
    acceleratedOrbit 9 214 = 103 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_214 : gap 9 214 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_214 : threshold 9 214 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_214 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 214) = 243 * (2 * m) + 103 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 214
  rw [data_9_214.1, data_9_214.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_214 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 214) = 243 * (2 * m + 1) + 103 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 214
  rw [data_9_214.1, data_9_214.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_214 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 214) < 512 * (2 * m) + 214 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 214 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_214] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 214) < 512 * (2 * m) + 214 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_214 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 214) < 512 * (2 * m + 1) + 214 := by
  apply refinement_cleared (k := 9) (r := 214) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_214]; decide

end Collatz.Research.RefinementAtlas.Batch190
