import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch060

/-- Complete interval computation for depth 9, residue 92. -/
theorem bounds_9_92 : exactInterval 9 92 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_92 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 92) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_92 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_92 : oddCount 92 9 = 3 ∧ acceleratedOrbit 9 92 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_92 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 92) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_92.1, data_9_92.2]

/-- Complete interval computation for depth 9, residue 93. -/
theorem bounds_9_93 : exactInterval 9 93 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_93 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 93) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_93 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_93 : oddCount 93 9 = 3 ∧ acceleratedOrbit 9 93 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_93 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 93) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_93.1, data_9_93.2]

/-- Complete interval computation for depth 9, residue 94. -/
theorem bounds_9_94 : exactInterval 9 94 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_94 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 94) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_94 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_94 : oddCount 94 9 = 6 ∧ acceleratedOrbit 9 94 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_94 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 94) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_94.1, data_9_94.2]

/-- Complete interval computation for depth 9, residue 95. -/
theorem bounds_9_95 : exactInterval 9 95 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_95 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 95) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_95 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_95 : oddCount 95 9 = 6 ∧ acceleratedOrbit 9 95 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_95 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 95) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_95.1, data_9_95.2]

/-- Complete interval computation for depth 9, residue 96. -/
theorem bounds_9_96 : exactInterval 9 96 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_96 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 96) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_96 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_96 : oddCount 96 9 = 2 ∧ acceleratedOrbit 9 96 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_96 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 96) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_96.1, data_9_96.2]

/-- Complete interval computation for depth 9, residue 97. -/
theorem bounds_9_97 : exactInterval 9 97 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_97 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 97) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_97 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_97 : oddCount 97 9 = 5 ∧ acceleratedOrbit 9 97 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_97 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 97) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_97.1, data_9_97.2]

/-- Complete interval computation for depth 9, residue 98. -/
theorem bounds_9_98 : exactInterval 9 98 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_98 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 98) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_98 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_98 : oddCount 98 9 = 4 ∧ acceleratedOrbit 9 98 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_98 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 98) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_98.1, data_9_98.2]

/-- Complete interval computation for depth 9, residue 99. -/
theorem bounds_9_99 : exactInterval 9 99 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_99 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 99) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_99 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_99 : oddCount 99 9 = 4 ∧ acceleratedOrbit 9 99 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_99 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 99) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_99.1, data_9_99.2]

/-- Complete interval computation for depth 9, residue 100. -/
theorem bounds_9_100 : exactInterval 9 100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_100 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 100) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_100 : oddCount 100 9 = 4 ∧ acceleratedOrbit 9 100 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_100 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 100) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_100.1, data_9_100.2]

/-- Complete interval computation for depth 9, residue 101. -/
theorem bounds_9_101 : exactInterval 9 101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_101 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 101) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_101 : oddCount 101 9 = 4 ∧ acceleratedOrbit 9 101 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_101 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 101) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_101.1, data_9_101.2]

/-- Complete interval computation for depth 9, residue 102. -/
theorem bounds_9_102 : exactInterval 9 102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_102 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 102) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_102 : oddCount 102 9 = 4 ∧ acceleratedOrbit 9 102 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_102 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 102) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_102.1, data_9_102.2]

end Collatz.Research.DescentIntervals.Batch060
