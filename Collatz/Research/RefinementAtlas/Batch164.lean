import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 164. -/
namespace Collatz.Research.RefinementAtlas.Batch164
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 104). -/
theorem data_9_104 : oddCount 104 9 = 2 ∧
    acceleratedOrbit 9 104 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_104 : gap 9 104 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_104 : threshold 9 104 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_104 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 104) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 104
  rw [data_9_104.1, data_9_104.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_104 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 104) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 104
  rw [data_9_104.1, data_9_104.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_104 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 104) < 512 * (2 * m) + 104 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 104 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_104] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 104) < 512 * (2 * m) + 104 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_104 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 104) < 512 * (2 * m + 1) + 104 := by
  apply refinement_cleared (k := 9) (r := 104) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_104]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 106). -/
theorem data_9_106 : oddCount 106 9 = 2 ∧
    acceleratedOrbit 9 106 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_106 : gap 9 106 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_106 : threshold 9 106 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_106 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 106) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 106
  rw [data_9_106.1, data_9_106.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_106 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 106) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 106
  rw [data_9_106.1, data_9_106.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_106 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 106) < 512 * (2 * m) + 106 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 106 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_106] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 106) < 512 * (2 * m) + 106 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_106 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 106) < 512 * (2 * m + 1) + 106 := by
  apply refinement_cleared (k := 9) (r := 106) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_106]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 112). -/
theorem data_9_112 : oddCount 112 9 = 4 ∧
    acceleratedOrbit 9 112 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_112 : gap 9 112 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_112 : threshold 9 112 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_112 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 112) = 81 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 112
  rw [data_9_112.1, data_9_112.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_112 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 112) = 81 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 112
  rw [data_9_112.1, data_9_112.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_112 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 112) < 512 * (2 * m) + 112 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 112 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_112] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 112) < 512 * (2 * m) + 112 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_112 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 112) < 512 * (2 * m + 1) + 112 := by
  apply refinement_cleared (k := 9) (r := 112) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_112]; decide

end Collatz.Research.RefinementAtlas.Batch164
