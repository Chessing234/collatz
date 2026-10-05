import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 299. -/
namespace Collatz.Research.RefinementAtlas.Batch299
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 138). -/
theorem data_10_138 : oddCount 138 10 = 3 ∧
    acceleratedOrbit 10 138 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_138 : gap 10 138 = 997 ∧ 27 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_138 : threshold 10 138 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_138 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 138) = 27 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 138
  rw [data_10_138.1, data_10_138.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_138 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 138) = 27 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 138
  rw [data_10_138.1, data_10_138.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_138 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 138) < 1024 * (2 * m) + 138 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 138 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_138] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 138) < 1024 * (2 * m) + 138 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_138 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 138) < 1024 * (2 * m + 1) + 138 := by
  apply refinement_cleared (k := 10) (r := 138) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_138]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 139). -/
theorem data_10_139 : oddCount 139 10 = 6 ∧
    acceleratedOrbit 10 139 = 101 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_139 : gap 10 139 = 295 ∧ 729 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_139 : threshold 10 139 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_139 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 139) = 729 * (2 * m) + 101 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 139
  rw [data_10_139.1, data_10_139.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_139 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 139) = 729 * (2 * m + 1) + 101 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 139
  rw [data_10_139.1, data_10_139.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_139 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 139) < 1024 * (2 * m) + 139 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 139 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_139] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 139) < 1024 * (2 * m) + 139 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_139 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 139) < 1024 * (2 * m + 1) + 139 := by
  apply refinement_cleared (k := 10) (r := 139) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_139]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 140). -/
theorem data_10_140 : oddCount 140 10 = 3 ∧
    acceleratedOrbit 10 140 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_140 : gap 10 140 = 997 ∧ 27 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_140 : threshold 10 140 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_140 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 140) = 27 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 140
  rw [data_10_140.1, data_10_140.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_140 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 140) = 27 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 140
  rw [data_10_140.1, data_10_140.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_140 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 140) < 1024 * (2 * m) + 140 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 140 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_140] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 140) < 1024 * (2 * m) + 140 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_140 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 140) < 1024 * (2 * m + 1) + 140 := by
  apply refinement_cleared (k := 10) (r := 140) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_140]; decide

end Collatz.Research.RefinementAtlas.Batch299
