import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch020

/-- Complete interval computation for depth 7, residue 68. -/
theorem bounds_7_68 : exactInterval 7 68 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_68 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 68) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_68 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_68 : oddCount 68 7 = 2 ∧ acceleratedOrbit 7 68 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_68 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 68) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_68.1, data_7_68.2]

/-- Complete interval computation for depth 7, residue 69. -/
theorem bounds_7_69 : exactInterval 7 69 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_69 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 69) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_69 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_69 : oddCount 69 7 = 2 ∧ acceleratedOrbit 7 69 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_69 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 69) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_69.1, data_7_69.2]

/-- Complete interval computation for depth 7, residue 70. -/
theorem bounds_7_70 : exactInterval 7 70 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_70 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 70) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_70 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_70 : oddCount 70 7 = 2 ∧ acceleratedOrbit 7 70 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_70 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 70) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_70.1, data_7_70.2]

/-- Complete interval computation for depth 7, residue 71. -/
theorem bounds_7_71 : exactInterval 7 71 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_71 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 71) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_71 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_71 : oddCount 71 7 = 5 ∧ acceleratedOrbit 7 71 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_71 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 71) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_71.1, data_7_71.2]

/-- Complete interval computation for depth 7, residue 72. -/
theorem bounds_7_72 : exactInterval 7 72 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_72 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 72) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_72 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_72 : oddCount 72 7 = 3 ∧ acceleratedOrbit 7 72 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_72 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 72) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_72.1, data_7_72.2]

/-- Complete interval computation for depth 7, residue 73. -/
theorem bounds_7_73 : exactInterval 7 73 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_73 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 73) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_73 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_73 : oddCount 73 7 = 4 ∧ acceleratedOrbit 7 73 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_73 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 73) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_73.1, data_7_73.2]

/-- Complete interval computation for depth 7, residue 74. -/
theorem bounds_7_74 : exactInterval 7 74 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_74 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 74) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_74 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_74 : oddCount 74 7 = 3 ∧ acceleratedOrbit 7 74 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_74 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 74) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_74.1, data_7_74.2]

/-- Complete interval computation for depth 7, residue 75. -/
theorem bounds_7_75 : exactInterval 7 75 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_75 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 75) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_75 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_75 : oddCount 75 7 = 3 ∧ acceleratedOrbit 7 75 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_75 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 75) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_75.1, data_7_75.2]

/-- Complete interval computation for depth 7, residue 76. -/
theorem bounds_7_76 : exactInterval 7 76 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_76 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 76) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_76 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_76 : oddCount 76 7 = 3 ∧ acceleratedOrbit 7 76 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_76 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 76) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_76.1, data_7_76.2]

/-- Complete interval computation for depth 7, residue 77. -/
theorem bounds_7_77 : exactInterval 7 77 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_77 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 77) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_77 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_77 : oddCount 77 7 = 3 ∧ acceleratedOrbit 7 77 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_77 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 77) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_77.1, data_7_77.2]

end Collatz.Research.DescentIntervals.Batch020
