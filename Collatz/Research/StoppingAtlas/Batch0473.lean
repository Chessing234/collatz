import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0473

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 81. -/
theorem bounds_13_81 : exactInterval 13 81 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_81 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 81) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_81 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_81 : oddCount 81 13 = 6 ∧ acceleratedOrbit 13 81 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_81 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 81) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_81.1, data_13_81.2]

/-- Complete interval computation for depth 13, residue 82. -/
theorem bounds_13_82 : exactInterval 13 82 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_82 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 82) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_82 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_82 : oddCount 82 13 = 9 ∧ acceleratedOrbit 13 82 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_82 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 82) = 3 ^ 9 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_82.1, data_13_82.2]

/-- Complete interval computation for depth 13, residue 83. -/
theorem bounds_13_83 : exactInterval 13 83 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_83 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 83) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_83 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_83 : oddCount 83 13 = 9 ∧ acceleratedOrbit 13 83 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_83 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 83) = 3 ^ 9 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_83.1, data_13_83.2]

/-- Complete interval computation for depth 13, residue 84. -/
theorem bounds_13_84 : exactInterval 13 84 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_84 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 84) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_84 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_84 : oddCount 84 13 = 4 ∧ acceleratedOrbit 13 84 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_84 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 84) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_84.1, data_13_84.2]

/-- Complete interval computation for depth 13, residue 85. -/
theorem bounds_13_85 : exactInterval 13 85 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_85 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 85) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_85 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_85 : oddCount 85 13 = 4 ∧ acceleratedOrbit 13 85 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_85 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 85) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_85.1, data_13_85.2]

/-- Complete interval computation for depth 13, residue 86. -/
theorem bounds_13_86 : exactInterval 13 86 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_86 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 86) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_86 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_86 : oddCount 86 13 = 7 ∧ acceleratedOrbit 13 86 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_86 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 86) = 3 ^ 7 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_86.1, data_13_86.2]

/-- Complete interval computation for depth 13, residue 87. -/
theorem bounds_13_87 : exactInterval 13 87 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_87 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 87) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_87 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_87 : oddCount 87 13 = 7 ∧ acceleratedOrbit 13 87 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_87 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 87) = 3 ^ 7 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_87.1, data_13_87.2]

/-- Complete interval computation for depth 13, residue 88. -/
theorem bounds_13_88 : exactInterval 13 88 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_88 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 88) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_88 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_88 : oddCount 88 13 = 4 ∧ acceleratedOrbit 13 88 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_88 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 88) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_88.1, data_13_88.2]

/-- Complete interval computation for depth 13, residue 89. -/
theorem bounds_13_89 : exactInterval 13 89 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_89 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 89) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_89 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_89 : oddCount 89 13 = 7 ∧ acceleratedOrbit 13 89 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_89 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 89) = 3 ^ 7 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_89.1, data_13_89.2]

/-- Complete interval computation for depth 13, residue 90. -/
theorem bounds_13_90 : exactInterval 13 90 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_90 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 90) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_90 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_90 : oddCount 90 13 = 4 ∧ acceleratedOrbit 13 90 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_90 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 90) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_90.1, data_13_90.2]

/-- Complete interval computation for depth 13, residue 91. -/
theorem bounds_13_91 : exactInterval 13 91 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_91 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 91) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_91 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_91 : oddCount 91 13 = 10 ∧ acceleratedOrbit 13 91 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_91 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 91) = 3 ^ 10 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_91.1, data_13_91.2]

/-- Complete interval computation for depth 13, residue 92. -/
theorem bounds_13_92 : exactInterval 13 92 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_92 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 92) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_92 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_92 : oddCount 92 13 = 4 ∧ acceleratedOrbit 13 92 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_92 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 92) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_92.1, data_13_92.2]

/-- Complete interval computation for depth 13, residue 93. -/
theorem bounds_13_93 : exactInterval 13 93 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_93 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 93) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_93 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_93 : oddCount 93 13 = 4 ∧ acceleratedOrbit 13 93 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_93 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 93) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_93.1, data_13_93.2]

/-- Complete interval computation for depth 13, residue 94. -/
theorem bounds_13_94 : exactInterval 13 94 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_94 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 94) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_94 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_94 : oddCount 94 13 = 9 ∧ acceleratedOrbit 13 94 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_94 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 94) = 3 ^ 9 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_94.1, data_13_94.2]

/-- Complete interval computation for depth 13, residue 95. -/
theorem bounds_13_95 : exactInterval 13 95 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_95 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 95) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_95 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_95 : oddCount 95 13 = 9 ∧ acceleratedOrbit 13 95 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_95 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 95) = 3 ^ 9 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_95.1, data_13_95.2]

/-- Complete interval computation for depth 13, residue 96. -/
theorem bounds_13_96 : exactInterval 13 96 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_96 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 96) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_96 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_96 : oddCount 96 13 = 4 ∧ acceleratedOrbit 13 96 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_96 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 96) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_96.1, data_13_96.2]

end Collatz.Research.StoppingAtlas.Batch0473
