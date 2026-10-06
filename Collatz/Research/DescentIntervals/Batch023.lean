import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch023

/-- Complete interval computation for depth 7, residue 98. -/
theorem bounds_7_98 : exactInterval 7 98 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_98 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 98) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_98 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_98 : oddCount 98 7 = 2 ∧ acceleratedOrbit 7 98 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_98 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 98) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_98.1, data_7_98.2]

/-- Complete interval computation for depth 7, residue 99. -/
theorem bounds_7_99 : exactInterval 7 99 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_99 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 99) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_99 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_99 : oddCount 99 7 = 2 ∧ acceleratedOrbit 7 99 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_99 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 99) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_99.1, data_7_99.2]

/-- Complete interval computation for depth 7, residue 100. -/
theorem bounds_7_100 : exactInterval 7 100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_100 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 100) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_100 : oddCount 100 7 = 3 ∧ acceleratedOrbit 7 100 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_100 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 100) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_100.1, data_7_100.2]

/-- Complete interval computation for depth 7, residue 101. -/
theorem bounds_7_101 : exactInterval 7 101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_101 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 101) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_101 : oddCount 101 7 = 3 ∧ acceleratedOrbit 7 101 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_101 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 101) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_101.1, data_7_101.2]

/-- Complete interval computation for depth 7, residue 102. -/
theorem bounds_7_102 : exactInterval 7 102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_102 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 102) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_102 : oddCount 102 7 = 3 ∧ acceleratedOrbit 7 102 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_102 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 102) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_102.1, data_7_102.2]

/-- Complete interval computation for depth 7, residue 103. -/
theorem bounds_7_103 : exactInterval 7 103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_103 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 103) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_103 : oddCount 103 7 = 6 ∧ acceleratedOrbit 7 103 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_103 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 103) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_103.1, data_7_103.2]

/-- Complete interval computation for depth 7, residue 104. -/
theorem bounds_7_104 : exactInterval 7 104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_104 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 104) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_104 : oddCount 104 7 = 2 ∧ acceleratedOrbit 7 104 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_104 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 104) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_104.1, data_7_104.2]

/-- Complete interval computation for depth 7, residue 105. -/
theorem bounds_7_105 : exactInterval 7 105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_105 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 105) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_105 : oddCount 105 7 = 5 ∧ acceleratedOrbit 7 105 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_105 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 105) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_105.1, data_7_105.2]

/-- Complete interval computation for depth 7, residue 106. -/
theorem bounds_7_106 : exactInterval 7 106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_106 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 106) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_106 : oddCount 106 7 = 2 ∧ acceleratedOrbit 7 106 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_106 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 106) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_106.1, data_7_106.2]

/-- Complete interval computation for depth 7, residue 107. -/
theorem bounds_7_107 : exactInterval 7 107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_107 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 107) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_107 : oddCount 107 7 = 5 ∧ acceleratedOrbit 7 107 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_107 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 107) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_107.1, data_7_107.2]

/-- Complete interval computation for depth 7, residue 108. -/
theorem bounds_7_108 : exactInterval 7 108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_108 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 108) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_108 : oddCount 108 7 = 4 ∧ acceleratedOrbit 7 108 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_108 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 108) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_108.1, data_7_108.2]

end Collatz.Research.DescentIntervals.Batch023
