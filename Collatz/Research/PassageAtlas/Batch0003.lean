import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0003

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 65. -/
theorem bounds_15_65 : exactInterval 15 65 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_65 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 65) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_65 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_65 : oddCount 65 15 = 7 ∧ acceleratedOrbit 15 65 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_65 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 65) = 3 ^ 7 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_65.1, data_15_65.2]

/-- Complete interval computation for depth 15, residue 66. -/
theorem bounds_15_66 : exactInterval 15 66 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_66 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 66) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_66 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_66 : oddCount 66 15 = 7 ∧ acceleratedOrbit 15 66 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_66 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 66) = 3 ^ 7 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_66.1, data_15_66.2]

/-- Complete interval computation for depth 15, residue 67. -/
theorem bounds_15_67 : exactInterval 15 67 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_67 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 67) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_67 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_67 : oddCount 67 15 = 7 ∧ acceleratedOrbit 15 67 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_67 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 67) = 3 ^ 7 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_67.1, data_15_67.2]

/-- Complete interval computation for depth 15, residue 68. -/
theorem bounds_15_68 : exactInterval 15 68 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_68 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 68) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_68 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_68 : oddCount 68 15 = 5 ∧ acceleratedOrbit 15 68 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_68 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 68) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_68.1, data_15_68.2]

/-- Complete interval computation for depth 15, residue 69. -/
theorem bounds_15_69 : exactInterval 15 69 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_69 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 69) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_69 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_69 : oddCount 69 15 = 5 ∧ acceleratedOrbit 15 69 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_69 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 69) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_69.1, data_15_69.2]

/-- Complete interval computation for depth 15, residue 70. -/
theorem bounds_15_70 : exactInterval 15 70 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_70 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 70) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_70 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_70 : oddCount 70 15 = 5 ∧ acceleratedOrbit 15 70 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_70 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 70) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_70.1, data_15_70.2]

/-- Complete interval computation for depth 15, residue 71. -/
theorem bounds_15_71 : exactInterval 15 71 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_71 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 71) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_71 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_71 : oddCount 71 15 = 11 ∧ acceleratedOrbit 15 71 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_71 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 71) = 3 ^ 11 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_71.1, data_15_71.2]

/-- Complete interval computation for depth 15, residue 72. -/
theorem bounds_15_72 : exactInterval 15 72 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_72 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 72) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_72 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_72 : oddCount 72 15 = 6 ∧ acceleratedOrbit 15 72 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_72 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 72) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_72.1, data_15_72.2]

/-- Complete interval computation for depth 15, residue 73. -/
theorem bounds_15_73 : exactInterval 15 73 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_73 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 73) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_73 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_73 : oddCount 73 15 = 10 ∧ acceleratedOrbit 15 73 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_73 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 73) = 3 ^ 10 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_73.1, data_15_73.2]

/-- Complete interval computation for depth 15, residue 74. -/
theorem bounds_15_74 : exactInterval 15 74 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_74 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 74) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_74 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_74 : oddCount 74 15 = 6 ∧ acceleratedOrbit 15 74 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_74 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 74) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_74.1, data_15_74.2]

/-- Complete interval computation for depth 15, residue 75. -/
theorem bounds_15_75 : exactInterval 15 75 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_75 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 75) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_75 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_75 : oddCount 75 15 = 5 ∧ acceleratedOrbit 15 75 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_75 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 75) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_75.1, data_15_75.2]

/-- Complete interval computation for depth 15, residue 76. -/
theorem bounds_15_76 : exactInterval 15 76 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_76 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 76) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_76 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_76 : oddCount 76 15 = 6 ∧ acceleratedOrbit 15 76 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_76 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 76) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_76.1, data_15_76.2]

/-- Complete interval computation for depth 15, residue 77. -/
theorem bounds_15_77 : exactInterval 15 77 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_77 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 77) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_77 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_77 : oddCount 77 15 = 6 ∧ acceleratedOrbit 15 77 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_77 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 77) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_77.1, data_15_77.2]

/-- Complete interval computation for depth 15, residue 78. -/
theorem bounds_15_78 : exactInterval 15 78 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_78 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 78) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_78 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_78 : oddCount 78 15 = 8 ∧ acceleratedOrbit 15 78 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_78 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 78) = 3 ^ 8 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_78.1, data_15_78.2]

/-- Complete interval computation for depth 15, residue 79. -/
theorem bounds_15_79 : exactInterval 15 79 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_79 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 79) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_79 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_79 : oddCount 79 15 = 8 ∧ acceleratedOrbit 15 79 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_79 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 79) = 3 ^ 8 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_79.1, data_15_79.2]

/-- Complete interval computation for depth 15, residue 80. -/
theorem bounds_15_80 : exactInterval 15 80 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_80 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 80) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_80 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_80 : oddCount 80 15 = 5 ∧ acceleratedOrbit 15 80 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_80 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 80) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_80.1, data_15_80.2]

/-- Complete interval computation for depth 15, residue 81. -/
theorem bounds_15_81 : exactInterval 15 81 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_81 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 81) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_81 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_81 : oddCount 81 15 = 6 ∧ acceleratedOrbit 15 81 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_81 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 81) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_81.1, data_15_81.2]

/-- Complete interval computation for depth 15, residue 82. -/
theorem bounds_15_82 : exactInterval 15 82 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_82 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 82) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_82 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_82 : oddCount 82 15 = 10 ∧ acceleratedOrbit 15 82 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_82 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 82) = 3 ^ 10 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_82.1, data_15_82.2]

/-- Complete interval computation for depth 15, residue 83. -/
theorem bounds_15_83 : exactInterval 15 83 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_83 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 83) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_83 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_83 : oddCount 83 15 = 10 ∧ acceleratedOrbit 15 83 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_83 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 83) = 3 ^ 10 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_83.1, data_15_83.2]

/-- Complete interval computation for depth 15, residue 84. -/
theorem bounds_15_84 : exactInterval 15 84 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_84 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 84) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_84 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_84 : oddCount 84 15 = 5 ∧ acceleratedOrbit 15 84 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_84 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 84) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_84.1, data_15_84.2]

/-- Complete interval computation for depth 15, residue 85. -/
theorem bounds_15_85 : exactInterval 15 85 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_85 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 85) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_85 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_85 : oddCount 85 15 = 5 ∧ acceleratedOrbit 15 85 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_85 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 85) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_85.1, data_15_85.2]

/-- Complete interval computation for depth 15, residue 86. -/
theorem bounds_15_86 : exactInterval 15 86 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_86 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 86) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_86 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_86 : oddCount 86 15 = 8 ∧ acceleratedOrbit 15 86 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_86 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 86) = 3 ^ 8 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_86.1, data_15_86.2]

/-- Complete interval computation for depth 15, residue 87. -/
theorem bounds_15_87 : exactInterval 15 87 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_87 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 87) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_87 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_87 : oddCount 87 15 = 8 ∧ acceleratedOrbit 15 87 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_87 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 87) = 3 ^ 8 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_87.1, data_15_87.2]

/-- Complete interval computation for depth 15, residue 88. -/
theorem bounds_15_88 : exactInterval 15 88 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_88 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 88) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_88 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_88 : oddCount 88 15 = 5 ∧ acceleratedOrbit 15 88 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_88 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 88) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_88.1, data_15_88.2]

/-- Complete interval computation for depth 15, residue 89. -/
theorem bounds_15_89 : exactInterval 15 89 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_89 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 89) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_89 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_89 : oddCount 89 15 = 8 ∧ acceleratedOrbit 15 89 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_89 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 89) = 3 ^ 8 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_89.1, data_15_89.2]

/-- Complete interval computation for depth 15, residue 90. -/
theorem bounds_15_90 : exactInterval 15 90 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_90 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 90) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_90 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_90 : oddCount 90 15 = 5 ∧ acceleratedOrbit 15 90 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_90 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 90) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_90.1, data_15_90.2]

/-- Complete interval computation for depth 15, residue 91. -/
theorem bounds_15_91 : exactInterval 15 91 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_91 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 91) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_91 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_91 : oddCount 91 15 = 10 ∧ acceleratedOrbit 15 91 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_91 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 91) = 3 ^ 10 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_91.1, data_15_91.2]

/-- Complete interval computation for depth 15, residue 92. -/
theorem bounds_15_92 : exactInterval 15 92 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_92 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 92) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_92 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_92 : oddCount 92 15 = 5 ∧ acceleratedOrbit 15 92 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_92 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 92) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_92.1, data_15_92.2]

/-- Complete interval computation for depth 15, residue 93. -/
theorem bounds_15_93 : exactInterval 15 93 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_93 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 93) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_93 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_93 : oddCount 93 15 = 5 ∧ acceleratedOrbit 15 93 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_93 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 93) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_93.1, data_15_93.2]

/-- Complete interval computation for depth 15, residue 94. -/
theorem bounds_15_94 : exactInterval 15 94 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_94 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 94) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_94 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_94 : oddCount 94 15 = 10 ∧ acceleratedOrbit 15 94 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_94 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 94) = 3 ^ 10 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_94.1, data_15_94.2]

/-- Complete interval computation for depth 15, residue 95. -/
theorem bounds_15_95 : exactInterval 15 95 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_95 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 95) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_95 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_95 : oddCount 95 15 = 10 ∧ acceleratedOrbit 15 95 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_95 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 95) = 3 ^ 10 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_95.1, data_15_95.2]

/-- Complete interval computation for depth 15, residue 96. -/
theorem bounds_15_96 : exactInterval 15 96 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_96 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 96) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_96 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_96 : oddCount 96 15 = 5 ∧ acceleratedOrbit 15 96 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_96 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 96) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_96.1, data_15_96.2]

/-- Complete interval computation for depth 15, residue 97. -/
theorem bounds_15_97 : exactInterval 15 97 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_97 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 97) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_97 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_97 : oddCount 97 15 = 10 ∧ acceleratedOrbit 15 97 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_97 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 97) = 3 ^ 10 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_97.1, data_15_97.2]

end Collatz.Research.PassageAtlas.Batch0003
