import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0073

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 81. -/
theorem bounds_11_81 : exactInterval 11 81 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_81 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 81) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_81 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_81 : oddCount 81 11 = 5 ∧ acceleratedOrbit 11 81 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_81 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 81) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_81.1, data_11_81.2]

/-- Complete interval computation for depth 11, residue 82. -/
theorem bounds_11_82 : exactInterval 11 82 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_82 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 82) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_82 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_82 : oddCount 82 11 = 7 ∧ acceleratedOrbit 11 82 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_82 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 82) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_82.1, data_11_82.2]

/-- Complete interval computation for depth 11, residue 83. -/
theorem bounds_11_83 : exactInterval 11 83 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_83 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 83) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_83 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_83 : oddCount 83 11 = 7 ∧ acceleratedOrbit 11 83 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_83 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 83) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_83.1, data_11_83.2]

/-- Complete interval computation for depth 11, residue 84. -/
theorem bounds_11_84 : exactInterval 11 84 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_84 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 84) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_84 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_84 : oddCount 84 11 = 3 ∧ acceleratedOrbit 11 84 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_84 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 84) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_84.1, data_11_84.2]

/-- Complete interval computation for depth 11, residue 85. -/
theorem bounds_11_85 : exactInterval 11 85 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_85 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 85) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_85 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_85 : oddCount 85 11 = 3 ∧ acceleratedOrbit 11 85 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_85 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 85) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_85.1, data_11_85.2]

/-- Complete interval computation for depth 11, residue 86. -/
theorem bounds_11_86 : exactInterval 11 86 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_86 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 86) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_86 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_86 : oddCount 86 11 = 5 ∧ acceleratedOrbit 11 86 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_86 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 86) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_86.1, data_11_86.2]

/-- Complete interval computation for depth 11, residue 87. -/
theorem bounds_11_87 : exactInterval 11 87 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_87 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 87) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_87 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_87 : oddCount 87 11 = 5 ∧ acceleratedOrbit 11 87 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_87 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 87) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_87.1, data_11_87.2]

/-- Complete interval computation for depth 11, residue 88. -/
theorem bounds_11_88 : exactInterval 11 88 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_88 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 88) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_88 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_88 : oddCount 88 11 = 4 ∧ acceleratedOrbit 11 88 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_88 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 88) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_88.1, data_11_88.2]

/-- Complete interval computation for depth 11, residue 89. -/
theorem bounds_11_89 : exactInterval 11 89 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_89 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 89) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_89 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_89 : oddCount 89 11 = 5 ∧ acceleratedOrbit 11 89 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_89 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 89) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_89.1, data_11_89.2]

/-- Complete interval computation for depth 11, residue 90. -/
theorem bounds_11_90 : exactInterval 11 90 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_90 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 90) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_90 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_90 : oddCount 90 11 = 4 ∧ acceleratedOrbit 11 90 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_90 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 90) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_90.1, data_11_90.2]

/-- Complete interval computation for depth 11, residue 91. -/
theorem bounds_11_91 : exactInterval 11 91 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_91 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 91) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_91 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_91 : oddCount 91 11 = 9 ∧ acceleratedOrbit 11 91 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_91 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 91) = 3 ^ 9 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_91.1, data_11_91.2]

/-- Complete interval computation for depth 11, residue 92. -/
theorem bounds_11_92 : exactInterval 11 92 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_92 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 92) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_92 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_92 : oddCount 92 11 = 4 ∧ acceleratedOrbit 11 92 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_92 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 92) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_92.1, data_11_92.2]

/-- Complete interval computation for depth 11, residue 93. -/
theorem bounds_11_93 : exactInterval 11 93 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_93 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 93) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_93 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_93 : oddCount 93 11 = 4 ∧ acceleratedOrbit 11 93 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_93 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 93) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_93.1, data_11_93.2]

/-- Complete interval computation for depth 11, residue 94. -/
theorem bounds_11_94 : exactInterval 11 94 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_94 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 94) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_94 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_94 : oddCount 94 11 = 7 ∧ acceleratedOrbit 11 94 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_94 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 94) = 3 ^ 7 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_94.1, data_11_94.2]

/-- Complete interval computation for depth 11, residue 95. -/
theorem bounds_11_95 : exactInterval 11 95 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_95 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 95) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_95 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_95 : oddCount 95 11 = 7 ∧ acceleratedOrbit 11 95 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_95 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 95) = 3 ^ 7 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_95.1, data_11_95.2]

/-- Complete interval computation for depth 11, residue 96. -/
theorem bounds_11_96 : exactInterval 11 96 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_96 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 96) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_96 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_96 : oddCount 96 11 = 3 ∧ acceleratedOrbit 11 96 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_96 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 96) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_96.1, data_11_96.2]

end Collatz.Research.StoppingAtlas.Batch0073
