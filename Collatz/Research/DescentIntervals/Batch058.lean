import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch058

/-- Complete interval computation for depth 9, residue 72. -/
theorem bounds_9_72 : exactInterval 9 72 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_72 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 72) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_72 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_72 : oddCount 72 9 = 4 ∧ acceleratedOrbit 9 72 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_72 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 72) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_72.1, data_9_72.2]

/-- Complete interval computation for depth 9, residue 73. -/
theorem bounds_9_73 : exactInterval 9 73 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_73 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 73) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_73 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_73 : oddCount 73 9 = 6 ∧ acceleratedOrbit 9 73 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_73 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 73) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_73.1, data_9_73.2]

/-- Complete interval computation for depth 9, residue 74. -/
theorem bounds_9_74 : exactInterval 9 74 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_74 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 74) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_74 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_74 : oddCount 74 9 = 4 ∧ acceleratedOrbit 9 74 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_74 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 74) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_74.1, data_9_74.2]

/-- Complete interval computation for depth 9, residue 75. -/
theorem bounds_9_75 : exactInterval 9 75 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_75 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 75) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_75 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_75 : oddCount 75 9 = 3 ∧ acceleratedOrbit 9 75 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_75 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 75) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_75.1, data_9_75.2]

/-- Complete interval computation for depth 9, residue 76. -/
theorem bounds_9_76 : exactInterval 9 76 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_76 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 76) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_76 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_76 : oddCount 76 9 = 4 ∧ acceleratedOrbit 9 76 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_76 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 76) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_76.1, data_9_76.2]

/-- Complete interval computation for depth 9, residue 77. -/
theorem bounds_9_77 : exactInterval 9 77 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_77 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 77) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_77 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_77 : oddCount 77 9 = 4 ∧ acceleratedOrbit 9 77 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_77 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 77) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_77.1, data_9_77.2]

/-- Complete interval computation for depth 9, residue 78. -/
theorem bounds_9_78 : exactInterval 9 78 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_78 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 78) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_78 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_78 : oddCount 78 9 = 5 ∧ acceleratedOrbit 9 78 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_78 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 78) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_78.1, data_9_78.2]

/-- Complete interval computation for depth 9, residue 79. -/
theorem bounds_9_79 : exactInterval 9 79 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_79 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 79) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_79 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_79 : oddCount 79 9 = 5 ∧ acceleratedOrbit 9 79 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_79 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 79) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_79.1, data_9_79.2]

/-- Complete interval computation for depth 9, residue 80. -/
theorem bounds_9_80 : exactInterval 9 80 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_80 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 80) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_80 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_80 : oddCount 80 9 = 2 ∧ acceleratedOrbit 9 80 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_80 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 80) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_80.1, data_9_80.2]

/-- Complete interval computation for depth 9, residue 81. -/
theorem bounds_9_81 : exactInterval 9 81 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_81 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 81) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_81 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_81 : oddCount 81 9 = 5 ∧ acceleratedOrbit 9 81 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_81 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 81) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_81.1, data_9_81.2]

end Collatz.Research.DescentIntervals.Batch058
