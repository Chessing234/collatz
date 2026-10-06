import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch032

/-- Complete interval computation for depth 8, residue 62. -/
theorem bounds_8_62 : exactInterval 8 62 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_62 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 62) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_62 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_62 : oddCount 62 8 = 6 ∧ acceleratedOrbit 8 62 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_62 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 62) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_62.1, data_8_62.2]

/-- Complete interval computation for depth 8, residue 63. -/
theorem bounds_8_63 : exactInterval 8 63 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_63 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 63) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_63 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_63 : oddCount 63 8 = 6 ∧ acceleratedOrbit 8 63 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_63 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 63) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_63.1, data_8_63.2]

/-- Complete interval computation for depth 8, residue 64. -/
theorem bounds_8_64 : exactInterval 8 64 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_64 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 64) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_64 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_64 : oddCount 64 8 = 1 ∧ acceleratedOrbit 8 64 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_64 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 64) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_64.1, data_8_64.2]

/-- Complete interval computation for depth 8, residue 65. -/
theorem bounds_8_65 : exactInterval 8 65 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_65 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 65) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_65 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_65 : oddCount 65 8 = 3 ∧ acceleratedOrbit 8 65 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_65 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 65) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_65.1, data_8_65.2]

/-- Complete interval computation for depth 8, residue 66. -/
theorem bounds_8_66 : exactInterval 8 66 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_66 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 66) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_66 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_66 : oddCount 66 8 = 4 ∧ acceleratedOrbit 8 66 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_66 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 66) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_66.1, data_8_66.2]

/-- Complete interval computation for depth 8, residue 67. -/
theorem bounds_8_67 : exactInterval 8 67 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_67 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 67) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_67 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_67 : oddCount 67 8 = 4 ∧ acceleratedOrbit 8 67 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_67 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 67) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_67.1, data_8_67.2]

/-- Complete interval computation for depth 8, residue 68. -/
theorem bounds_8_68 : exactInterval 8 68 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_68 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 68) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_68 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_68 : oddCount 68 8 = 3 ∧ acceleratedOrbit 8 68 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_68 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 68) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_68.1, data_8_68.2]

/-- Complete interval computation for depth 8, residue 69. -/
theorem bounds_8_69 : exactInterval 8 69 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_69 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 69) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_69 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_69 : oddCount 69 8 = 3 ∧ acceleratedOrbit 8 69 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_69 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 69) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_69.1, data_8_69.2]

/-- Complete interval computation for depth 8, residue 70. -/
theorem bounds_8_70 : exactInterval 8 70 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_70 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 70) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_70 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_70 : oddCount 70 8 = 3 ∧ acceleratedOrbit 8 70 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_70 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 70) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_70.1, data_8_70.2]

/-- Complete interval computation for depth 8, residue 71. -/
theorem bounds_8_71 : exactInterval 8 71 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_71 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 71) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_71 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_71 : oddCount 71 8 = 6 ∧ acceleratedOrbit 8 71 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_71 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 71) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_71.1, data_8_71.2]

/-- Complete interval computation for depth 8, residue 72. -/
theorem bounds_8_72 : exactInterval 8 72 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_72 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 72) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_72 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_72 : oddCount 72 8 = 4 ∧ acceleratedOrbit 8 72 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_72 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 72) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_72.1, data_8_72.2]

end Collatz.Research.DescentIntervals.Batch032
