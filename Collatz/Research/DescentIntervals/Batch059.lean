import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch059

/-- Complete interval computation for depth 9, residue 82. -/
theorem bounds_9_82 : exactInterval 9 82 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_82 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 82) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_82 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_82 : oddCount 82 9 = 6 ∧ acceleratedOrbit 9 82 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_82 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 82) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_82.1, data_9_82.2]

/-- Complete interval computation for depth 9, residue 83. -/
theorem bounds_9_83 : exactInterval 9 83 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_83 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 83) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_83 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_83 : oddCount 83 9 = 6 ∧ acceleratedOrbit 9 83 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_83 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 83) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_83.1, data_9_83.2]

/-- Complete interval computation for depth 9, residue 84. -/
theorem bounds_9_84 : exactInterval 9 84 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_84 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 84) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_84 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_84 : oddCount 84 9 = 2 ∧ acceleratedOrbit 9 84 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_84 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 84) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_84.1, data_9_84.2]

/-- Complete interval computation for depth 9, residue 85. -/
theorem bounds_9_85 : exactInterval 9 85 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_85 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 85) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_85 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_85 : oddCount 85 9 = 2 ∧ acceleratedOrbit 9 85 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_85 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 85) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_85.1, data_9_85.2]

/-- Complete interval computation for depth 9, residue 86. -/
theorem bounds_9_86 : exactInterval 9 86 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_86 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 86) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_86 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_86 : oddCount 86 9 = 4 ∧ acceleratedOrbit 9 86 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_86 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 86) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_86.1, data_9_86.2]

/-- Complete interval computation for depth 9, residue 87. -/
theorem bounds_9_87 : exactInterval 9 87 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_87 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 87) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_87 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_87 : oddCount 87 9 = 4 ∧ acceleratedOrbit 9 87 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_87 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 87) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_87.1, data_9_87.2]

/-- Complete interval computation for depth 9, residue 88. -/
theorem bounds_9_88 : exactInterval 9 88 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_88 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 88) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_88 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_88 : oddCount 88 9 = 3 ∧ acceleratedOrbit 9 88 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_88 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 88) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_88.1, data_9_88.2]

/-- Complete interval computation for depth 9, residue 89. -/
theorem bounds_9_89 : exactInterval 9 89 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_89 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 89) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_89 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_89 : oddCount 89 9 = 5 ∧ acceleratedOrbit 9 89 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_89 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 89) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_89.1, data_9_89.2]

/-- Complete interval computation for depth 9, residue 90. -/
theorem bounds_9_90 : exactInterval 9 90 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_90 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 90) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_90 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_90 : oddCount 90 9 = 3 ∧ acceleratedOrbit 9 90 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_90 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 90) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_90.1, data_9_90.2]

/-- Complete interval computation for depth 9, residue 91. -/
theorem bounds_9_91 : exactInterval 9 91 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_91 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 91) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_91 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_91 : oddCount 91 9 = 7 ∧ acceleratedOrbit 9 91 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_91 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 91) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_91.1, data_9_91.2]

end Collatz.Research.DescentIntervals.Batch059
