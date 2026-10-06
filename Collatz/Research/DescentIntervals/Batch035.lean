import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch035

/-- Complete interval computation for depth 8, residue 93. -/
theorem bounds_8_93 : exactInterval 8 93 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_93 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 93) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_93 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_93 : oddCount 93 8 = 3 ∧ acceleratedOrbit 8 93 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_93 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 93) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_93.1, data_8_93.2]

/-- Complete interval computation for depth 8, residue 94. -/
theorem bounds_8_94 : exactInterval 8 94 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_94 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 94) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_94 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_94 : oddCount 94 8 = 5 ∧ acceleratedOrbit 8 94 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_94 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 94) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_94.1, data_8_94.2]

/-- Complete interval computation for depth 8, residue 95. -/
theorem bounds_8_95 : exactInterval 8 95 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_95 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 95) 8 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_95 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_95 : oddCount 95 8 = 5 ∧ acceleratedOrbit 8 95 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_95 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 95) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_95.1, data_8_95.2]

/-- Complete interval computation for depth 8, residue 96. -/
theorem bounds_8_96 : exactInterval 8 96 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_96 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 96) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_96 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_96 : oddCount 96 8 = 2 ∧ acceleratedOrbit 8 96 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_96 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 96) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_96.1, data_8_96.2]

/-- Complete interval computation for depth 8, residue 97. -/
theorem bounds_8_97 : exactInterval 8 97 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_97 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 97) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_97 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_97 : oddCount 97 8 = 5 ∧ acceleratedOrbit 8 97 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_97 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 97) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_97.1, data_8_97.2]

/-- Complete interval computation for depth 8, residue 98. -/
theorem bounds_8_98 : exactInterval 8 98 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_98 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 98) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_98 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_98 : oddCount 98 8 = 3 ∧ acceleratedOrbit 8 98 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_98 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 98) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_98.1, data_8_98.2]

/-- Complete interval computation for depth 8, residue 99. -/
theorem bounds_8_99 : exactInterval 8 99 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_99 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 99) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_99 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_99 : oddCount 99 8 = 3 ∧ acceleratedOrbit 8 99 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_99 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 99) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_99.1, data_8_99.2]

/-- Complete interval computation for depth 8, residue 100. -/
theorem bounds_8_100 : exactInterval 8 100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_100 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 100) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_100 : oddCount 100 8 = 3 ∧ acceleratedOrbit 8 100 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_100 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 100) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_100.1, data_8_100.2]

/-- Complete interval computation for depth 8, residue 101. -/
theorem bounds_8_101 : exactInterval 8 101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_101 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 101) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_101 : oddCount 101 8 = 3 ∧ acceleratedOrbit 8 101 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_101 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 101) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_101.1, data_8_101.2]

/-- Complete interval computation for depth 8, residue 102. -/
theorem bounds_8_102 : exactInterval 8 102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_102 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 102) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_102 : oddCount 102 8 = 3 ∧ acceleratedOrbit 8 102 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_102 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 102) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_102.1, data_8_102.2]

end Collatz.Research.DescentIntervals.Batch035
