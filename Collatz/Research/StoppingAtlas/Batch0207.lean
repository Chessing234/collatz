import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0207

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 92. -/
theorem bounds_12_92 : exactInterval 12 92 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_92 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 92) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_92 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_92 : oddCount 92 12 = 4 ∧ acceleratedOrbit 12 92 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_92 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 92) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_92.1, data_12_92.2]

/-- Complete interval computation for depth 12, residue 93. -/
theorem bounds_12_93 : exactInterval 12 93 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_93 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 93) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_93 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_93 : oddCount 93 12 = 4 ∧ acceleratedOrbit 12 93 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_93 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 93) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_93.1, data_12_93.2]

/-- Complete interval computation for depth 12, residue 94. -/
theorem bounds_12_94 : exactInterval 12 94 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_94 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 94) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_94 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_94 : oddCount 94 12 = 8 ∧ acceleratedOrbit 12 94 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_94 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 94) = 3 ^ 8 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_94.1, data_12_94.2]

/-- Complete interval computation for depth 12, residue 95. -/
theorem bounds_12_95 : exactInterval 12 95 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_95 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 95) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_95 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_95 : oddCount 95 12 = 8 ∧ acceleratedOrbit 12 95 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_95 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 95) = 3 ^ 8 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_95.1, data_12_95.2]

/-- Complete interval computation for depth 12, residue 96. -/
theorem bounds_12_96 : exactInterval 12 96 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_96 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 96) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_96 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_96 : oddCount 96 12 = 3 ∧ acceleratedOrbit 12 96 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_96 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 96) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_96.1, data_12_96.2]

/-- Complete interval computation for depth 12, residue 97. -/
theorem bounds_12_97 : exactInterval 12 97 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_97 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 97) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_97 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_97 : oddCount 97 12 = 8 ∧ acceleratedOrbit 12 97 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_97 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 97) = 3 ^ 8 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_97.1, data_12_97.2]

/-- Complete interval computation for depth 12, residue 98. -/
theorem bounds_12_98 : exactInterval 12 98 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_98 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 98) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_98 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_98 : oddCount 98 12 = 6 ∧ acceleratedOrbit 12 98 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_98 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 98) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_98.1, data_12_98.2]

/-- Complete interval computation for depth 12, residue 99. -/
theorem bounds_12_99 : exactInterval 12 99 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_99 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 99) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_99 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_99 : oddCount 99 12 = 6 ∧ acceleratedOrbit 12 99 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_99 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 99) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_99.1, data_12_99.2]

/-- Complete interval computation for depth 12, residue 100. -/
theorem bounds_12_100 : exactInterval 12 100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_100 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 100) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_100 : oddCount 100 12 = 6 ∧ acceleratedOrbit 12 100 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_100 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 100) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_100.1, data_12_100.2]

/-- Complete interval computation for depth 12, residue 101. -/
theorem bounds_12_101 : exactInterval 12 101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_101 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 101) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_101 : oddCount 101 12 = 6 ∧ acceleratedOrbit 12 101 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_101 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 101) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_101.1, data_12_101.2]

/-- Complete interval computation for depth 12, residue 102. -/
theorem bounds_12_102 : exactInterval 12 102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_102 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 102) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_102 : oddCount 102 12 = 6 ∧ acceleratedOrbit 12 102 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_102 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 102) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_102.1, data_12_102.2]

/-- Complete interval computation for depth 12, residue 103. -/
theorem bounds_12_103 : exactInterval 12 103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_103 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 103) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_103 : oddCount 103 12 = 8 ∧ acceleratedOrbit 12 103 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_103 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 103) = 3 ^ 8 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_103.1, data_12_103.2]

/-- Complete interval computation for depth 12, residue 104. -/
theorem bounds_12_104 : exactInterval 12 104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_104 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 104) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_104 : oddCount 104 12 = 3 ∧ acceleratedOrbit 12 104 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_104 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 104) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_104.1, data_12_104.2]

/-- Complete interval computation for depth 12, residue 105. -/
theorem bounds_12_105 : exactInterval 12 105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_105 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 105) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_105 : oddCount 105 12 = 6 ∧ acceleratedOrbit 12 105 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_105 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 105) = 3 ^ 6 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_105.1, data_12_105.2]

/-- Complete interval computation for depth 12, residue 106. -/
theorem bounds_12_106 : exactInterval 12 106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_106 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 106) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_106 : oddCount 106 12 = 3 ∧ acceleratedOrbit 12 106 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_106 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 106) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_106.1, data_12_106.2]

end Collatz.Research.StoppingAtlas.Batch0207
