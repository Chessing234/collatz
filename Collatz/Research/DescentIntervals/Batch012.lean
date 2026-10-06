import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch012

/-- Complete interval computation for depth 6, residue 50. -/
theorem bounds_6_50 : exactInterval 6 50 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_50 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 50) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_50 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_50 : oddCount 50 6 = 3 ∧ acceleratedOrbit 6 50 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_50 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 50) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_50.1, data_6_50.2]

/-- Complete interval computation for depth 6, residue 51. -/
theorem bounds_6_51 : exactInterval 6 51 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_51 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 51) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_51 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_51 : oddCount 51 6 = 3 ∧ acceleratedOrbit 6 51 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_51 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 51) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_51.1, data_6_51.2]

/-- Complete interval computation for depth 6, residue 52. -/
theorem bounds_6_52 : exactInterval 6 52 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_52 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 52) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_52 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_52 : oddCount 52 6 = 2 ∧ acceleratedOrbit 6 52 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_52 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 52) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_52.1, data_6_52.2]

/-- Complete interval computation for depth 6, residue 53. -/
theorem bounds_6_53 : exactInterval 6 53 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_53 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 53) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_53 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_53 : oddCount 53 6 = 2 ∧ acceleratedOrbit 6 53 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_53 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 53) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_53.1, data_6_53.2]

/-- Complete interval computation for depth 6, residue 54. -/
theorem bounds_6_54 : exactInterval 6 54 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_54 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 54) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_54 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_54 : oddCount 54 6 = 4 ∧ acceleratedOrbit 6 54 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_54 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 54) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_54.1, data_6_54.2]

/-- Complete interval computation for depth 6, residue 55. -/
theorem bounds_6_55 : exactInterval 6 55 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_55 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 55) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_55 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_55 : oddCount 55 6 = 4 ∧ acceleratedOrbit 6 55 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_55 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 55) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_55.1, data_6_55.2]

/-- Complete interval computation for depth 6, residue 56. -/
theorem bounds_6_56 : exactInterval 6 56 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_56 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 56) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_56 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_56 : oddCount 56 6 = 3 ∧ acceleratedOrbit 6 56 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_56 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 56) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_56.1, data_6_56.2]

/-- Complete interval computation for depth 6, residue 57. -/
theorem bounds_6_57 : exactInterval 6 57 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_57 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 57) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_57 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_57 : oddCount 57 6 = 4 ∧ acceleratedOrbit 6 57 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_57 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 57) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_57.1, data_6_57.2]

/-- Complete interval computation for depth 6, residue 58. -/
theorem bounds_6_58 : exactInterval 6 58 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_58 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 58) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_58 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_58 : oddCount 58 6 = 3 ∧ acceleratedOrbit 6 58 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_58 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 58) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_58.1, data_6_58.2]

/-- Complete interval computation for depth 6, residue 59. -/
theorem bounds_6_59 : exactInterval 6 59 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_59 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 59) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_59 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_59 : oddCount 59 6 = 4 ∧ acceleratedOrbit 6 59 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_59 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 59) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_59.1, data_6_59.2]

end Collatz.Research.DescentIntervals.Batch012
