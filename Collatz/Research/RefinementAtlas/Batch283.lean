import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 283. -/
namespace Collatz.Research.RefinementAtlas.Batch283
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 76). -/
theorem data_10_76 : oddCount 76 10 = 5 ∧
    acceleratedOrbit 10 76 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_76 : gap 10 76 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_76 : threshold 10 76 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_76 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 76) = 243 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 76
  rw [data_10_76.1, data_10_76.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_76 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 76) = 243 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 76
  rw [data_10_76.1, data_10_76.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_76 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 76) < 1024 * (2 * m) + 76 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 76 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_76] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 76) < 1024 * (2 * m) + 76 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_76 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 76) < 1024 * (2 * m + 1) + 76 := by
  apply refinement_cleared (k := 10) (r := 76) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_76]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 77). -/
theorem data_10_77 : oddCount 77 10 = 5 ∧
    acceleratedOrbit 10 77 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_77 : gap 10 77 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_77 : threshold 10 77 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_77 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 77) = 243 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 77
  rw [data_10_77.1, data_10_77.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_77 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 77) = 243 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 77
  rw [data_10_77.1, data_10_77.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_77 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 77) < 1024 * (2 * m) + 77 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 77 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_77] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 77) < 1024 * (2 * m) + 77 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_77 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 77) < 1024 * (2 * m + 1) + 77 := by
  apply refinement_cleared (k := 10) (r := 77) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_77]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 78). -/
theorem data_10_78 : oddCount 78 10 = 5 ∧
    acceleratedOrbit 10 78 = 19 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_78 : gap 10 78 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_78 : threshold 10 78 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_78 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 78) = 243 * (2 * m) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 78
  rw [data_10_78.1, data_10_78.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_78 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 78) = 243 * (2 * m + 1) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 78
  rw [data_10_78.1, data_10_78.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_78 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 78) < 1024 * (2 * m) + 78 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 78 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_78] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 78) < 1024 * (2 * m) + 78 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_78 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 78) < 1024 * (2 * m + 1) + 78 := by
  apply refinement_cleared (k := 10) (r := 78) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_78]; decide

end Collatz.Research.RefinementAtlas.Batch283
