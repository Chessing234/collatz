import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch019

/-- Complete interval computation for depth 7, residue 57. -/
theorem bounds_7_57 : exactInterval 7 57 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_57 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 57) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_57 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_57 : oddCount 57 7 = 4 ∧ acceleratedOrbit 7 57 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_57 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 57) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_57.1, data_7_57.2]

/-- Complete interval computation for depth 7, residue 58. -/
theorem bounds_7_58 : exactInterval 7 58 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_58 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 58) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_58 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_58 : oddCount 58 7 = 3 ∧ acceleratedOrbit 7 58 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_58 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 58) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_58.1, data_7_58.2]

/-- Complete interval computation for depth 7, residue 59. -/
theorem bounds_7_59 : exactInterval 7 59 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_59 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 59) 7 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_59 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_59 : oddCount 59 7 = 4 ∧ acceleratedOrbit 7 59 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_59 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 59) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_59.1, data_7_59.2]

/-- Complete interval computation for depth 7, residue 60. -/
theorem bounds_7_60 : exactInterval 7 60 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_60 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 60) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_60 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_60 : oddCount 60 7 = 4 ∧ acceleratedOrbit 7 60 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_60 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 60) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_60.1, data_7_60.2]

/-- Complete interval computation for depth 7, residue 61. -/
theorem bounds_7_61 : exactInterval 7 61 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_61 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 61) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_61 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_61 : oddCount 61 7 = 4 ∧ acceleratedOrbit 7 61 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_61 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 61) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_61.1, data_7_61.2]

/-- Complete interval computation for depth 7, residue 62. -/
theorem bounds_7_62 : exactInterval 7 62 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_62 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 62) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_62 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_62 : oddCount 62 7 = 5 ∧ acceleratedOrbit 7 62 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_62 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 62) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_62.1, data_7_62.2]

/-- Complete interval computation for depth 7, residue 63. -/
theorem bounds_7_63 : exactInterval 7 63 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_63 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 63) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_63 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_63 : oddCount 63 7 = 6 ∧ acceleratedOrbit 7 63 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_63 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 63) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_63.1, data_7_63.2]

/-- Complete interval computation for depth 7, residue 64. -/
theorem bounds_7_64 : exactInterval 7 64 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_64 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 64) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_64 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_64 : oddCount 64 7 = 1 ∧ acceleratedOrbit 7 64 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_64 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 64) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_64.1, data_7_64.2]

/-- Complete interval computation for depth 7, residue 65. -/
theorem bounds_7_65 : exactInterval 7 65 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_65 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 65) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_65 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_65 : oddCount 65 7 = 3 ∧ acceleratedOrbit 7 65 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_65 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 65) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_65.1, data_7_65.2]

/-- Complete interval computation for depth 7, residue 66. -/
theorem bounds_7_66 : exactInterval 7 66 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_66 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 66) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_66 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_66 : oddCount 66 7 = 4 ∧ acceleratedOrbit 7 66 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_66 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 66) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_66.1, data_7_66.2]

/-- Complete interval computation for depth 7, residue 67. -/
theorem bounds_7_67 : exactInterval 7 67 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_67 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 67) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_67 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_67 : oddCount 67 7 = 4 ∧ acceleratedOrbit 7 67 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_67 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 67) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_67.1, data_7_67.2]

end Collatz.Research.DescentIntervals.Batch019
