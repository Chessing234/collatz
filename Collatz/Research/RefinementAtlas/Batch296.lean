import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 296. -/
namespace Collatz.Research.RefinementAtlas.Batch296
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 128). -/
theorem data_10_128 : oddCount 128 10 = 2 ∧
    acceleratedOrbit 10 128 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_128 : gap 10 128 = 1015 ∧ 9 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_128 : threshold 10 128 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_128 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 128) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 128
  rw [data_10_128.1, data_10_128.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_128 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 128) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 128
  rw [data_10_128.1, data_10_128.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_128 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 128) < 1024 * (2 * m) + 128 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 128 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_128] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 128) < 1024 * (2 * m) + 128 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_128 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 128) < 1024 * (2 * m + 1) + 128 := by
  apply refinement_cleared (k := 10) (r := 128) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_128]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 129). -/
theorem data_10_129 : oddCount 129 10 = 6 ∧
    acceleratedOrbit 10 129 = 94 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_129 : gap 10 129 = 295 ∧ 729 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_129 : threshold 10 129 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_129 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 129) = 729 * (2 * m) + 94 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 129
  rw [data_10_129.1, data_10_129.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_129 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 129) = 729 * (2 * m + 1) + 94 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 129
  rw [data_10_129.1, data_10_129.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_129 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 129) < 1024 * (2 * m) + 129 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 129 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_129] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 129) < 1024 * (2 * m) + 129 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_129 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 129) < 1024 * (2 * m + 1) + 129 := by
  apply refinement_cleared (k := 10) (r := 129) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_129]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 130). -/
theorem data_10_130 : oddCount 130 10 = 4 ∧
    acceleratedOrbit 10 130 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_130 : gap 10 130 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_130 : threshold 10 130 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_130 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 130) = 81 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 130
  rw [data_10_130.1, data_10_130.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_130 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 130) = 81 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 130
  rw [data_10_130.1, data_10_130.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_130 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 130) < 1024 * (2 * m) + 130 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 130 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_130] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 130) < 1024 * (2 * m) + 130 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_130 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 130) < 1024 * (2 * m + 1) + 130 := by
  apply refinement_cleared (k := 10) (r := 130) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_130]; decide

end Collatz.Research.RefinementAtlas.Batch296
