import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0206

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 76. -/
theorem bounds_12_76 : exactInterval 12 76 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_76 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 76) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_76 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_76 : oddCount 76 12 = 5 ∧ acceleratedOrbit 12 76 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_76 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 76) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_76.1, data_12_76.2]

/-- Complete interval computation for depth 12, residue 77. -/
theorem bounds_12_77 : exactInterval 12 77 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_77 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 77) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_77 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_77 : oddCount 77 12 = 5 ∧ acceleratedOrbit 12 77 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_77 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 77) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_77.1, data_12_77.2]

/-- Complete interval computation for depth 12, residue 78. -/
theorem bounds_12_78 : exactInterval 12 78 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_78 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 78) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_78 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_78 : oddCount 78 12 = 7 ∧ acceleratedOrbit 12 78 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_78 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 78) = 3 ^ 7 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_78.1, data_12_78.2]

/-- Complete interval computation for depth 12, residue 79. -/
theorem bounds_12_79 : exactInterval 12 79 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_79 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 79) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_79 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_79 : oddCount 79 12 = 7 ∧ acceleratedOrbit 12 79 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_79 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 79) = 3 ^ 7 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_79.1, data_12_79.2]

/-- Complete interval computation for depth 12, residue 80. -/
theorem bounds_12_80 : exactInterval 12 80 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_80 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 80) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_80 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_80 : oddCount 80 12 = 3 ∧ acceleratedOrbit 12 80 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_80 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 80) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_80.1, data_12_80.2]

/-- Complete interval computation for depth 12, residue 81. -/
theorem bounds_12_81 : exactInterval 12 81 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_81 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 81) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_81 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_81 : oddCount 81 12 = 5 ∧ acceleratedOrbit 12 81 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_81 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 81) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_81.1, data_12_81.2]

/-- Complete interval computation for depth 12, residue 82. -/
theorem bounds_12_82 : exactInterval 12 82 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_82 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 82) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_82 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_82 : oddCount 82 12 = 8 ∧ acceleratedOrbit 12 82 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_82 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 82) = 3 ^ 8 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_82.1, data_12_82.2]

/-- Complete interval computation for depth 12, residue 83. -/
theorem bounds_12_83 : exactInterval 12 83 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_83 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 83) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_83 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_83 : oddCount 83 12 = 8 ∧ acceleratedOrbit 12 83 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_83 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 83) = 3 ^ 8 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_83.1, data_12_83.2]

/-- Complete interval computation for depth 12, residue 84. -/
theorem bounds_12_84 : exactInterval 12 84 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_84 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 84) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_84 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_84 : oddCount 84 12 = 3 ∧ acceleratedOrbit 12 84 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_84 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 84) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_84.1, data_12_84.2]

/-- Complete interval computation for depth 12, residue 85. -/
theorem bounds_12_85 : exactInterval 12 85 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_85 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 85) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_85 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_85 : oddCount 85 12 = 3 ∧ acceleratedOrbit 12 85 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_85 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 85) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_85.1, data_12_85.2]

/-- Complete interval computation for depth 12, residue 86. -/
theorem bounds_12_86 : exactInterval 12 86 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_86 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 86) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_86 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_86 : oddCount 86 12 = 6 ∧ acceleratedOrbit 12 86 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_86 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 86) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_86.1, data_12_86.2]

/-- Complete interval computation for depth 12, residue 87. -/
theorem bounds_12_87 : exactInterval 12 87 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_87 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 87) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_87 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_87 : oddCount 87 12 = 6 ∧ acceleratedOrbit 12 87 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_87 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 87) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_87.1, data_12_87.2]

/-- Complete interval computation for depth 12, residue 88. -/
theorem bounds_12_88 : exactInterval 12 88 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_88 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 88) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_88 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_88 : oddCount 88 12 = 4 ∧ acceleratedOrbit 12 88 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_88 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 88) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_88.1, data_12_88.2]

/-- Complete interval computation for depth 12, residue 89. -/
theorem bounds_12_89 : exactInterval 12 89 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_89 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 89) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_89 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_89 : oddCount 89 12 = 6 ∧ acceleratedOrbit 12 89 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_89 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 89) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_89.1, data_12_89.2]

/-- Complete interval computation for depth 12, residue 90. -/
theorem bounds_12_90 : exactInterval 12 90 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_90 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 90) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_90 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_90 : oddCount 90 12 = 4 ∧ acceleratedOrbit 12 90 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_90 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 90) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_90.1, data_12_90.2]

/-- Complete interval computation for depth 12, residue 91. -/
theorem bounds_12_91 : exactInterval 12 91 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_91 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 91) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_91 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_91 : oddCount 91 12 = 9 ∧ acceleratedOrbit 12 91 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_91 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 91) = 3 ^ 9 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_91.1, data_12_91.2]

end Collatz.Research.StoppingAtlas.Batch0206
