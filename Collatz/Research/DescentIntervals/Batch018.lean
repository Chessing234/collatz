import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch018

/-- Complete interval computation for depth 7, residue 47. -/
theorem bounds_7_47 : exactInterval 7 47 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_47 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 47) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_47 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_47 : oddCount 47 7 = 5 ∧ acceleratedOrbit 7 47 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_47 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 47) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_47.1, data_7_47.2]

/-- Complete interval computation for depth 7, residue 48. -/
theorem bounds_7_48 : exactInterval 7 48 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_48 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 48) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_48 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_48 : oddCount 48 7 = 2 ∧ acceleratedOrbit 7 48 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_48 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 48) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_48.1, data_7_48.2]

/-- Complete interval computation for depth 7, residue 49. -/
theorem bounds_7_49 : exactInterval 7 49 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_49 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 49) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_49 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_49 : oddCount 49 7 = 3 ∧ acceleratedOrbit 7 49 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_49 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 49) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_49.1, data_7_49.2]

/-- Complete interval computation for depth 7, residue 50. -/
theorem bounds_7_50 : exactInterval 7 50 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_50 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 50) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_50 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_50 : oddCount 50 7 = 3 ∧ acceleratedOrbit 7 50 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_50 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 50) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_50.1, data_7_50.2]

/-- Complete interval computation for depth 7, residue 51. -/
theorem bounds_7_51 : exactInterval 7 51 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_51 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 51) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_51 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_51 : oddCount 51 7 = 3 ∧ acceleratedOrbit 7 51 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_51 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 51) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_51.1, data_7_51.2]

/-- Complete interval computation for depth 7, residue 52. -/
theorem bounds_7_52 : exactInterval 7 52 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_52 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 52) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_52 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_52 : oddCount 52 7 = 2 ∧ acceleratedOrbit 7 52 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_52 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 52) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_52.1, data_7_52.2]

/-- Complete interval computation for depth 7, residue 53. -/
theorem bounds_7_53 : exactInterval 7 53 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_53 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 53) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_53 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_53 : oddCount 53 7 = 2 ∧ acceleratedOrbit 7 53 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_53 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 53) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_53.1, data_7_53.2]

/-- Complete interval computation for depth 7, residue 54. -/
theorem bounds_7_54 : exactInterval 7 54 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_54 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 54) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_54 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_54 : oddCount 54 7 = 5 ∧ acceleratedOrbit 7 54 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_54 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 54) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_54.1, data_7_54.2]

/-- Complete interval computation for depth 7, residue 55. -/
theorem bounds_7_55 : exactInterval 7 55 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_55 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 55) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_55 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_55 : oddCount 55 7 = 5 ∧ acceleratedOrbit 7 55 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_55 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 55) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_55.1, data_7_55.2]

/-- Complete interval computation for depth 7, residue 56. -/
theorem bounds_7_56 : exactInterval 7 56 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_56 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 56) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_56 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_56 : oddCount 56 7 = 3 ∧ acceleratedOrbit 7 56 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_56 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 56) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_56.1, data_7_56.2]

end Collatz.Research.DescentIntervals.Batch018
