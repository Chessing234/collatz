import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 298. -/
namespace Collatz.Research.RefinementAtlas.Batch298
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 134). -/
theorem data_10_134 : oddCount 134 10 = 4 ∧
    acceleratedOrbit 10 134 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_134 : gap 10 134 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_134 : threshold 10 134 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_134 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 134) = 81 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 134
  rw [data_10_134.1, data_10_134.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_134 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 134) = 81 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 134
  rw [data_10_134.1, data_10_134.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_134 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 134) < 1024 * (2 * m) + 134 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 134 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_134] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 134) < 1024 * (2 * m) + 134 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_134 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 134) < 1024 * (2 * m + 1) + 134 := by
  apply refinement_cleared (k := 10) (r := 134) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_134]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 135). -/
theorem data_10_135 : oddCount 135 10 = 6 ∧
    acceleratedOrbit 10 135 = 98 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_135 : gap 10 135 = 295 ∧ 729 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_135 : threshold 10 135 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_135 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 135) = 729 * (2 * m) + 98 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 135
  rw [data_10_135.1, data_10_135.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_135 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 135) = 729 * (2 * m + 1) + 98 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 135
  rw [data_10_135.1, data_10_135.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_135 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 135) < 1024 * (2 * m) + 135 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 135 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_135] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 135) < 1024 * (2 * m) + 135 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_135 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 135) < 1024 * (2 * m + 1) + 135 := by
  apply refinement_cleared (k := 10) (r := 135) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_135]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 136). -/
theorem data_10_136 : oddCount 136 10 = 3 ∧
    acceleratedOrbit 10 136 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_136 : gap 10 136 = 997 ∧ 27 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_136 : threshold 10 136 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_136 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 136) = 27 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 136
  rw [data_10_136.1, data_10_136.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_136 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 136) = 27 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 136
  rw [data_10_136.1, data_10_136.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_136 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 136) < 1024 * (2 * m) + 136 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 136 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_136] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 136) < 1024 * (2 * m) + 136 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_136 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 136) < 1024 * (2 * m + 1) + 136 := by
  apply refinement_cleared (k := 10) (r := 136) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_136]; decide

end Collatz.Research.RefinementAtlas.Batch298
