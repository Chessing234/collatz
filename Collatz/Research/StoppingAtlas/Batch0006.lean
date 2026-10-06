import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0006

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 76. -/
theorem bounds_10_76 : exactInterval 10 76 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_76 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 76) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_76 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_76 : oddCount 76 10 = 5 ∧ acceleratedOrbit 10 76 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_76 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 76) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_76.1, data_10_76.2]

/-- Complete interval computation for depth 10, residue 77. -/
theorem bounds_10_77 : exactInterval 10 77 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_77 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 77) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_77 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_77 : oddCount 77 10 = 5 ∧ acceleratedOrbit 10 77 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_77 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 77) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_77.1, data_10_77.2]

/-- Complete interval computation for depth 10, residue 78. -/
theorem bounds_10_78 : exactInterval 10 78 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_78 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 78) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_78 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_78 : oddCount 78 10 = 5 ∧ acceleratedOrbit 10 78 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_78 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 78) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_78.1, data_10_78.2]

/-- Complete interval computation for depth 10, residue 79. -/
theorem bounds_10_79 : exactInterval 10 79 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_79 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 79) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_79 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_79 : oddCount 79 10 = 5 ∧ acceleratedOrbit 10 79 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_79 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 79) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_79.1, data_10_79.2]

/-- Complete interval computation for depth 10, residue 80. -/
theorem bounds_10_80 : exactInterval 10 80 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_80 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 80) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_80 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_80 : oddCount 80 10 = 2 ∧ acceleratedOrbit 10 80 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_80 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 80) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_80.1, data_10_80.2]

/-- Complete interval computation for depth 10, residue 81. -/
theorem bounds_10_81 : exactInterval 10 81 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_81 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 81) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_81 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_81 : oddCount 81 10 = 5 ∧ acceleratedOrbit 10 81 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_81 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 81) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_81.1, data_10_81.2]

/-- Complete interval computation for depth 10, residue 82. -/
theorem bounds_10_82 : exactInterval 10 82 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_82 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 82) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_82 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_82 : oddCount 82 10 = 7 ∧ acceleratedOrbit 10 82 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_82 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 82) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_82.1, data_10_82.2]

/-- Complete interval computation for depth 10, residue 83. -/
theorem bounds_10_83 : exactInterval 10 83 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_83 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 83) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_83 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_83 : oddCount 83 10 = 7 ∧ acceleratedOrbit 10 83 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_83 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 83) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_83.1, data_10_83.2]

/-- Complete interval computation for depth 10, residue 84. -/
theorem bounds_10_84 : exactInterval 10 84 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_84 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 84) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_84 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_84 : oddCount 84 10 = 2 ∧ acceleratedOrbit 10 84 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_84 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 84) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_84.1, data_10_84.2]

/-- Complete interval computation for depth 10, residue 85. -/
theorem bounds_10_85 : exactInterval 10 85 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_85 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 85) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_85 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_85 : oddCount 85 10 = 2 ∧ acceleratedOrbit 10 85 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_85 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 85) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_85.1, data_10_85.2]

/-- Complete interval computation for depth 10, residue 86. -/
theorem bounds_10_86 : exactInterval 10 86 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_86 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 86) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_86 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_86 : oddCount 86 10 = 4 ∧ acceleratedOrbit 10 86 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_86 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 86) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_86.1, data_10_86.2]

/-- Complete interval computation for depth 10, residue 87. -/
theorem bounds_10_87 : exactInterval 10 87 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_87 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 87) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_87 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_87 : oddCount 87 10 = 4 ∧ acceleratedOrbit 10 87 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_87 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 87) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_87.1, data_10_87.2]

/-- Complete interval computation for depth 10, residue 88. -/
theorem bounds_10_88 : exactInterval 10 88 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_88 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 88) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_88 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_88 : oddCount 88 10 = 4 ∧ acceleratedOrbit 10 88 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_88 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 88) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_88.1, data_10_88.2]

/-- Complete interval computation for depth 10, residue 89. -/
theorem bounds_10_89 : exactInterval 10 89 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_89 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 89) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_89 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_89 : oddCount 89 10 = 5 ∧ acceleratedOrbit 10 89 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_89 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 89) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_89.1, data_10_89.2]

/-- Complete interval computation for depth 10, residue 90. -/
theorem bounds_10_90 : exactInterval 10 90 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_90 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 90) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_90 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_90 : oddCount 90 10 = 4 ∧ acceleratedOrbit 10 90 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_90 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 90) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_90.1, data_10_90.2]

/-- Complete interval computation for depth 10, residue 91. -/
theorem bounds_10_91 : exactInterval 10 91 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_91 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 91) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_91 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_91 : oddCount 91 10 = 8 ∧ acceleratedOrbit 10 91 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_91 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 91) = 3 ^ 8 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_91.1, data_10_91.2]

end Collatz.Research.StoppingAtlas.Batch0006
