import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 234. -/
namespace Collatz.Research.RefinementAtlas.Batch234
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 388). -/
theorem data_9_388 : oddCount 388 9 = 5 ∧
    acceleratedOrbit 9 388 = 188 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_388 : gap 9 388 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_388 : threshold 9 388 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_388 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 388) = 243 * (2 * m) + 188 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 388
  rw [data_9_388.1, data_9_388.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_388 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 388) = 243 * (2 * m + 1) + 188 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 388
  rw [data_9_388.1, data_9_388.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_388 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 388) < 512 * (2 * m) + 388 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 388 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_388] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 388) < 512 * (2 * m) + 388 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_388 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 388) < 512 * (2 * m + 1) + 388 := by
  apply refinement_cleared (k := 9) (r := 388) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_388]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 389). -/
theorem data_9_389 : oddCount 389 9 = 5 ∧
    acceleratedOrbit 9 389 = 188 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_389 : gap 9 389 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_389 : threshold 9 389 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_389 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 389) = 243 * (2 * m) + 188 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 389
  rw [data_9_389.1, data_9_389.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_389 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 389) = 243 * (2 * m + 1) + 188 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 389
  rw [data_9_389.1, data_9_389.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_389 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 389) < 512 * (2 * m) + 389 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 389 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_389] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 389) < 512 * (2 * m) + 389 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_389 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 389) < 512 * (2 * m + 1) + 389 := by
  apply refinement_cleared (k := 9) (r := 389) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_389]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 390). -/
theorem data_9_390 : oddCount 390 9 = 5 ∧
    acceleratedOrbit 9 390 = 188 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_390 : gap 9 390 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_390 : threshold 9 390 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_390 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 390) = 243 * (2 * m) + 188 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 390
  rw [data_9_390.1, data_9_390.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_390 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 390) = 243 * (2 * m + 1) + 188 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 390
  rw [data_9_390.1, data_9_390.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_390 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 390) < 512 * (2 * m) + 390 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 390 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_390] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 390) < 512 * (2 * m) + 390 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_390 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 390) < 512 * (2 * m + 1) + 390 := by
  apply refinement_cleared (k := 9) (r := 390) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_390]; decide

end Collatz.Research.RefinementAtlas.Batch234
