import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch021

/-- Complete interval computation for depth 7, residue 78. -/
theorem bounds_7_78 : exactInterval 7 78 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_78 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 78) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_78 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_78 : oddCount 78 7 = 5 ∧ acceleratedOrbit 7 78 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_78 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 78) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_78.1, data_7_78.2]

/-- Complete interval computation for depth 7, residue 79. -/
theorem bounds_7_79 : exactInterval 7 79 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_79 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 79) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_79 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_79 : oddCount 79 7 = 5 ∧ acceleratedOrbit 7 79 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_79 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 79) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_79.1, data_7_79.2]

/-- Complete interval computation for depth 7, residue 80. -/
theorem bounds_7_80 : exactInterval 7 80 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_80 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 80) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_80 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_80 : oddCount 80 7 = 1 ∧ acceleratedOrbit 7 80 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_80 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 80) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_80.1, data_7_80.2]

/-- Complete interval computation for depth 7, residue 81. -/
theorem bounds_7_81 : exactInterval 7 81 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_81 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 81) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_81 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_81 : oddCount 81 7 = 4 ∧ acceleratedOrbit 7 81 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_81 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 81) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_81.1, data_7_81.2]

/-- Complete interval computation for depth 7, residue 82. -/
theorem bounds_7_82 : exactInterval 7 82 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_82 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 82) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_82 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_82 : oddCount 82 7 = 5 ∧ acceleratedOrbit 7 82 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_82 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 82) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_82.1, data_7_82.2]

/-- Complete interval computation for depth 7, residue 83. -/
theorem bounds_7_83 : exactInterval 7 83 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_83 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 83) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_83 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_83 : oddCount 83 7 = 5 ∧ acceleratedOrbit 7 83 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_83 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 83) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_83.1, data_7_83.2]

/-- Complete interval computation for depth 7, residue 84. -/
theorem bounds_7_84 : exactInterval 7 84 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_84 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 84) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_84 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_84 : oddCount 84 7 = 1 ∧ acceleratedOrbit 7 84 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_84 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 84) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_84.1, data_7_84.2]

/-- Complete interval computation for depth 7, residue 85. -/
theorem bounds_7_85 : exactInterval 7 85 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_85 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 85) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_85 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_85 : oddCount 85 7 = 1 ∧ acceleratedOrbit 7 85 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_85 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 85) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_85.1, data_7_85.2]

/-- Complete interval computation for depth 7, residue 86. -/
theorem bounds_7_86 : exactInterval 7 86 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_86 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 86) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_86 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_86 : oddCount 86 7 = 4 ∧ acceleratedOrbit 7 86 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_86 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 86) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_86.1, data_7_86.2]

/-- Complete interval computation for depth 7, residue 87. -/
theorem bounds_7_87 : exactInterval 7 87 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_87 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 87) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_87 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_87 : oddCount 87 7 = 4 ∧ acceleratedOrbit 7 87 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_87 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 87) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_87.1, data_7_87.2]

end Collatz.Research.DescentIntervals.Batch021
