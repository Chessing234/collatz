import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 291. -/
namespace Collatz.Research.RefinementAtlas.Batch291
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 106). -/
theorem data_10_106 : oddCount 106 10 = 2 ∧
    acceleratedOrbit 10 106 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_106 : gap 10 106 = 1015 ∧ 9 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_106 : threshold 10 106 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_106 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 106) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 106
  rw [data_10_106.1, data_10_106.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_106 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 106) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 106
  rw [data_10_106.1, data_10_106.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_106 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 106) < 1024 * (2 * m) + 106 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 106 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_106] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 106) < 1024 * (2 * m) + 106 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_106 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 106) < 1024 * (2 * m + 1) + 106 := by
  apply refinement_cleared (k := 10) (r := 106) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_106]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 112). -/
theorem data_10_112 : oddCount 112 10 = 4 ∧
    acceleratedOrbit 10 112 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_112 : gap 10 112 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_112 : threshold 10 112 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_112 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 112) = 81 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 112
  rw [data_10_112.1, data_10_112.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_112 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 112) = 81 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 112
  rw [data_10_112.1, data_10_112.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_112 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 112) < 1024 * (2 * m) + 112 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 112 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_112] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 112) < 1024 * (2 * m) + 112 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_112 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 112) < 1024 * (2 * m + 1) + 112 := by
  apply refinement_cleared (k := 10) (r := 112) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_112]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 113). -/
theorem data_10_113 : oddCount 113 10 = 2 ∧
    acceleratedOrbit 10 113 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_113 : gap 10 113 = 1015 ∧ 9 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_113 : threshold 10 113 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_113 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 113) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 113
  rw [data_10_113.1, data_10_113.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_113 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 113) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 113
  rw [data_10_113.1, data_10_113.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_113 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 113) < 1024 * (2 * m) + 113 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 113 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_113] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 113) < 1024 * (2 * m) + 113 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_113 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 113) < 1024 * (2 * m + 1) + 113 := by
  apply refinement_cleared (k := 10) (r := 113) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_113]; decide

end Collatz.Research.RefinementAtlas.Batch291
