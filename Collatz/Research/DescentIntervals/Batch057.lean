import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch057

/-- Complete interval computation for depth 9, residue 62. -/
theorem bounds_9_62 : exactInterval 9 62 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_62 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 62) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_62 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_62 : oddCount 62 9 = 6 ∧ acceleratedOrbit 9 62 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_62 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 62) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_62.1, data_9_62.2]

/-- Complete interval computation for depth 9, residue 63. -/
theorem bounds_9_63 : exactInterval 9 63 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_63 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 63) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_63 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_63 : oddCount 63 9 = 6 ∧ acceleratedOrbit 9 63 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_63 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 63) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_63.1, data_9_63.2]

/-- Complete interval computation for depth 9, residue 64. -/
theorem bounds_9_64 : exactInterval 9 64 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_64 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 64) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_64 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_64 : oddCount 64 9 = 2 ∧ acceleratedOrbit 9 64 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_64 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 64) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_64.1, data_9_64.2]

/-- Complete interval computation for depth 9, residue 65. -/
theorem bounds_9_65 : exactInterval 9 65 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_65 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 65) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_65 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_65 : oddCount 65 9 = 4 ∧ acceleratedOrbit 9 65 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_65 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 65) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_65.1, data_9_65.2]

/-- Complete interval computation for depth 9, residue 66. -/
theorem bounds_9_66 : exactInterval 9 66 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_66 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 66) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_66 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_66 : oddCount 66 9 = 4 ∧ acceleratedOrbit 9 66 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_66 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 66) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_66.1, data_9_66.2]

/-- Complete interval computation for depth 9, residue 67. -/
theorem bounds_9_67 : exactInterval 9 67 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_67 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 67) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_67 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_67 : oddCount 67 9 = 4 ∧ acceleratedOrbit 9 67 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_67 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 67) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_67.1, data_9_67.2]

/-- Complete interval computation for depth 9, residue 68. -/
theorem bounds_9_68 : exactInterval 9 68 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_68 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 68) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_68 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_68 : oddCount 68 9 = 3 ∧ acceleratedOrbit 9 68 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_68 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 68) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_68.1, data_9_68.2]

/-- Complete interval computation for depth 9, residue 69. -/
theorem bounds_9_69 : exactInterval 9 69 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_69 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 69) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_69 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_69 : oddCount 69 9 = 3 ∧ acceleratedOrbit 9 69 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_69 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 69) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_69.1, data_9_69.2]

/-- Complete interval computation for depth 9, residue 70. -/
theorem bounds_9_70 : exactInterval 9 70 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_70 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 70) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_70 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_70 : oddCount 70 9 = 3 ∧ acceleratedOrbit 9 70 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_70 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 70) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_70.1, data_9_70.2]

/-- Complete interval computation for depth 9, residue 71. -/
theorem bounds_9_71 : exactInterval 9 71 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_71 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 71) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_71 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_71 : oddCount 71 9 = 6 ∧ acceleratedOrbit 9 71 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_71 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 71) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_71.1, data_9_71.2]

end Collatz.Research.DescentIntervals.Batch057
