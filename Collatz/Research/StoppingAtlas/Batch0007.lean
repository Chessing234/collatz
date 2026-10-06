import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0007

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 92. -/
theorem bounds_10_92 : exactInterval 10 92 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_92 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 92) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_92 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_92 : oddCount 92 10 = 4 ∧ acceleratedOrbit 10 92 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_92 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 92) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_92.1, data_10_92.2]

/-- Complete interval computation for depth 10, residue 93. -/
theorem bounds_10_93 : exactInterval 10 93 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_93 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 93) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_93 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_93 : oddCount 93 10 = 4 ∧ acceleratedOrbit 10 93 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_93 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 93) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_93.1, data_10_93.2]

/-- Complete interval computation for depth 10, residue 94. -/
theorem bounds_10_94 : exactInterval 10 94 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_94 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 94) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_94 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_94 : oddCount 94 10 = 7 ∧ acceleratedOrbit 10 94 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_94 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 94) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_94.1, data_10_94.2]

/-- Complete interval computation for depth 10, residue 95. -/
theorem bounds_10_95 : exactInterval 10 95 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_95 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 95) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_95 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_95 : oddCount 95 10 = 7 ∧ acceleratedOrbit 10 95 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_95 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 95) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_95.1, data_10_95.2]

/-- Complete interval computation for depth 10, residue 96. -/
theorem bounds_10_96 : exactInterval 10 96 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_96 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 96) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_96 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_96 : oddCount 96 10 = 2 ∧ acceleratedOrbit 10 96 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_96 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 96) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_96.1, data_10_96.2]

/-- Complete interval computation for depth 10, residue 97. -/
theorem bounds_10_97 : exactInterval 10 97 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_97 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 97) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_97 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_97 : oddCount 97 10 = 6 ∧ acceleratedOrbit 10 97 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_97 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 97) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_97.1, data_10_97.2]

/-- Complete interval computation for depth 10, residue 98. -/
theorem bounds_10_98 : exactInterval 10 98 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_98 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 98) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_98 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_98 : oddCount 98 10 = 5 ∧ acceleratedOrbit 10 98 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_98 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 98) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_98.1, data_10_98.2]

/-- Complete interval computation for depth 10, residue 99. -/
theorem bounds_10_99 : exactInterval 10 99 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_99 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 99) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_99 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_99 : oddCount 99 10 = 5 ∧ acceleratedOrbit 10 99 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_99 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 99) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_99.1, data_10_99.2]

/-- Complete interval computation for depth 10, residue 100. -/
theorem bounds_10_100 : exactInterval 10 100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_100 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 100) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_100 : oddCount 100 10 = 5 ∧ acceleratedOrbit 10 100 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_100 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 100) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_100.1, data_10_100.2]

/-- Complete interval computation for depth 10, residue 101. -/
theorem bounds_10_101 : exactInterval 10 101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_101 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 101) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_101 : oddCount 101 10 = 5 ∧ acceleratedOrbit 10 101 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_101 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 101) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_101.1, data_10_101.2]

/-- Complete interval computation for depth 10, residue 102. -/
theorem bounds_10_102 : exactInterval 10 102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_102 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 102) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_102 : oddCount 102 10 = 5 ∧ acceleratedOrbit 10 102 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_102 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 102) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_102.1, data_10_102.2]

/-- Complete interval computation for depth 10, residue 103. -/
theorem bounds_10_103 : exactInterval 10 103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_103 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 103) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_103 : oddCount 103 10 = 8 ∧ acceleratedOrbit 10 103 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_103 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 103) = 3 ^ 8 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_103.1, data_10_103.2]

/-- Complete interval computation for depth 10, residue 104. -/
theorem bounds_10_104 : exactInterval 10 104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_104 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 104) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_104 : oddCount 104 10 = 2 ∧ acceleratedOrbit 10 104 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_104 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 104) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_104.1, data_10_104.2]

/-- Complete interval computation for depth 10, residue 105. -/
theorem bounds_10_105 : exactInterval 10 105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_105 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 105) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_105 : oddCount 105 10 = 6 ∧ acceleratedOrbit 10 105 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_105 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 105) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_105.1, data_10_105.2]

/-- Complete interval computation for depth 10, residue 106. -/
theorem bounds_10_106 : exactInterval 10 106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_106 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 106) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_106 : oddCount 106 10 = 2 ∧ acceleratedOrbit 10 106 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_106 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 106) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_106.1, data_10_106.2]

end Collatz.Research.StoppingAtlas.Batch0007
