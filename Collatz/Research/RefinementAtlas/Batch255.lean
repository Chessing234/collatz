import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 255. -/
namespace Collatz.Research.RefinementAtlas.Batch255
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 474). -/
theorem data_9_474 : oddCount 474 9 = 4 ∧
    acceleratedOrbit 9 474 = 76 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_474 : gap 9 474 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_474 : threshold 9 474 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_474 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 474) = 81 * (2 * m) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 474
  rw [data_9_474.1, data_9_474.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_474 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 474) = 81 * (2 * m + 1) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 474
  rw [data_9_474.1, data_9_474.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_474 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 474) < 512 * (2 * m) + 474 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 474 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_474] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 474) < 512 * (2 * m) + 474 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_474 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 474) < 512 * (2 * m + 1) + 474 := by
  apply refinement_cleared (k := 9) (r := 474) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_474]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 475). -/
theorem data_9_475 : oddCount 475 9 = 5 ∧
    acceleratedOrbit 9 475 = 226 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_475 : gap 9 475 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_475 : threshold 9 475 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_475 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 475) = 243 * (2 * m) + 226 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 475
  rw [data_9_475.1, data_9_475.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_475 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 475) = 243 * (2 * m + 1) + 226 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 475
  rw [data_9_475.1, data_9_475.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_475 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 475) < 512 * (2 * m) + 475 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 475 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_475] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 475) < 512 * (2 * m) + 475 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_475 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 475) < 512 * (2 * m + 1) + 475 := by
  apply refinement_cleared (k := 9) (r := 475) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_475]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 476). -/
theorem data_9_476 : oddCount 476 9 = 4 ∧
    acceleratedOrbit 9 476 = 76 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_476 : gap 9 476 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_476 : threshold 9 476 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_476 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 476) = 81 * (2 * m) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 476
  rw [data_9_476.1, data_9_476.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_476 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 476) = 81 * (2 * m + 1) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 476
  rw [data_9_476.1, data_9_476.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_476 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 476) < 512 * (2 * m) + 476 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 476 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_476] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 476) < 512 * (2 * m) + 476 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_476 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 476) < 512 * (2 * m + 1) + 476 := by
  apply refinement_cleared (k := 9) (r := 476) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_476]; decide

end Collatz.Research.RefinementAtlas.Batch255
