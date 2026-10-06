import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch034

/-- Complete interval computation for depth 8, residue 83. -/
theorem bounds_8_83 : exactInterval 8 83 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_83 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 83) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_83 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_83 : oddCount 83 8 = 6 ∧ acceleratedOrbit 8 83 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_83 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 83) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_83.1, data_8_83.2]

/-- Complete interval computation for depth 8, residue 84. -/
theorem bounds_8_84 : exactInterval 8 84 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_84 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 84) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_84 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_84 : oddCount 84 8 = 1 ∧ acceleratedOrbit 8 84 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_84 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 84) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_84.1, data_8_84.2]

/-- Complete interval computation for depth 8, residue 85. -/
theorem bounds_8_85 : exactInterval 8 85 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_85 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 85) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_85 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_85 : oddCount 85 8 = 1 ∧ acceleratedOrbit 8 85 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_85 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 85) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_85.1, data_8_85.2]

/-- Complete interval computation for depth 8, residue 86. -/
theorem bounds_8_86 : exactInterval 8 86 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_86 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 86) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_86 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_86 : oddCount 86 8 = 4 ∧ acceleratedOrbit 8 86 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_86 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 86) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_86.1, data_8_86.2]

/-- Complete interval computation for depth 8, residue 87. -/
theorem bounds_8_87 : exactInterval 8 87 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_87 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 87) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_87 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_87 : oddCount 87 8 = 4 ∧ acceleratedOrbit 8 87 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_87 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 87) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_87.1, data_8_87.2]

/-- Complete interval computation for depth 8, residue 88. -/
theorem bounds_8_88 : exactInterval 8 88 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_88 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 88) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_88 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_88 : oddCount 88 8 = 3 ∧ acceleratedOrbit 8 88 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_88 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 88) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_88.1, data_8_88.2]

/-- Complete interval computation for depth 8, residue 89. -/
theorem bounds_8_89 : exactInterval 8 89 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_89 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 89) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_89 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_89 : oddCount 89 8 = 4 ∧ acceleratedOrbit 8 89 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_89 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 89) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_89.1, data_8_89.2]

/-- Complete interval computation for depth 8, residue 90. -/
theorem bounds_8_90 : exactInterval 8 90 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_90 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 90) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_90 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_90 : oddCount 90 8 = 3 ∧ acceleratedOrbit 8 90 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_90 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 90) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_90.1, data_8_90.2]

/-- Complete interval computation for depth 8, residue 91. -/
theorem bounds_8_91 : exactInterval 8 91 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_91 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 91) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_91 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_91 : oddCount 91 8 = 6 ∧ acceleratedOrbit 8 91 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_91 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 91) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_91.1, data_8_91.2]

/-- Complete interval computation for depth 8, residue 92. -/
theorem bounds_8_92 : exactInterval 8 92 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_92 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 92) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_92 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_92 : oddCount 92 8 = 3 ∧ acceleratedOrbit 8 92 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_92 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 92) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_92.1, data_8_92.2]

end Collatz.Research.DescentIntervals.Batch034
