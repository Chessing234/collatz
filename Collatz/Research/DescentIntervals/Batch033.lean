import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch033

/-- Complete interval computation for depth 8, residue 73. -/
theorem bounds_8_73 : exactInterval 8 73 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_73 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 73) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_73 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_73 : oddCount 73 8 = 5 ∧ acceleratedOrbit 8 73 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_73 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 73) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_73.1, data_8_73.2]

/-- Complete interval computation for depth 8, residue 74. -/
theorem bounds_8_74 : exactInterval 8 74 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_74 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 74) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_74 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_74 : oddCount 74 8 = 4 ∧ acceleratedOrbit 8 74 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_74 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 74) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_74.1, data_8_74.2]

/-- Complete interval computation for depth 8, residue 75. -/
theorem bounds_8_75 : exactInterval 8 75 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_75 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 75) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_75 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_75 : oddCount 75 8 = 3 ∧ acceleratedOrbit 8 75 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_75 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 75) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_75.1, data_8_75.2]

/-- Complete interval computation for depth 8, residue 76. -/
theorem bounds_8_76 : exactInterval 8 76 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_76 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 76) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_76 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_76 : oddCount 76 8 = 4 ∧ acceleratedOrbit 8 76 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_76 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 76) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_76.1, data_8_76.2]

/-- Complete interval computation for depth 8, residue 77. -/
theorem bounds_8_77 : exactInterval 8 77 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_77 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 77) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_77 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_77 : oddCount 77 8 = 4 ∧ acceleratedOrbit 8 77 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_77 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 77) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_77.1, data_8_77.2]

/-- Complete interval computation for depth 8, residue 78. -/
theorem bounds_8_78 : exactInterval 8 78 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_78 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 78) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_78 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_78 : oddCount 78 8 = 5 ∧ acceleratedOrbit 8 78 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_78 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 78) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_78.1, data_8_78.2]

/-- Complete interval computation for depth 8, residue 79. -/
theorem bounds_8_79 : exactInterval 8 79 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_79 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 79) 8 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_79 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_79 : oddCount 79 8 = 5 ∧ acceleratedOrbit 8 79 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_79 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 79) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_79.1, data_8_79.2]

/-- Complete interval computation for depth 8, residue 80. -/
theorem bounds_8_80 : exactInterval 8 80 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_80 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 80) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_80 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_80 : oddCount 80 8 = 1 ∧ acceleratedOrbit 8 80 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_80 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 80) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_80.1, data_8_80.2]

/-- Complete interval computation for depth 8, residue 81. -/
theorem bounds_8_81 : exactInterval 8 81 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_81 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 81) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_81 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_81 : oddCount 81 8 = 5 ∧ acceleratedOrbit 8 81 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_81 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 81) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_81.1, data_8_81.2]

/-- Complete interval computation for depth 8, residue 82. -/
theorem bounds_8_82 : exactInterval 8 82 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_82 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 82) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_82 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_82 : oddCount 82 8 = 6 ∧ acceleratedOrbit 8 82 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_82 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 82) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_82.1, data_8_82.2]

end Collatz.Research.DescentIntervals.Batch033
