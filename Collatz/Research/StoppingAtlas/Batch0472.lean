import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0472

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 66. -/
theorem bounds_13_66 : exactInterval 13 66 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_66 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 66) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_66 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_66 : oddCount 66 13 = 7 ∧ acceleratedOrbit 13 66 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_66 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 66) = 3 ^ 7 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_66.1, data_13_66.2]

/-- Complete interval computation for depth 13, residue 67. -/
theorem bounds_13_67 : exactInterval 13 67 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_67 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 67) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_67 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_67 : oddCount 67 13 = 7 ∧ acceleratedOrbit 13 67 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_67 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 67) = 3 ^ 7 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_67.1, data_13_67.2]

/-- Complete interval computation for depth 13, residue 68. -/
theorem bounds_13_68 : exactInterval 13 68 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_68 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 68) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_68 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_68 : oddCount 68 13 = 4 ∧ acceleratedOrbit 13 68 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_68 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 68) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_68.1, data_13_68.2]

/-- Complete interval computation for depth 13, residue 69. -/
theorem bounds_13_69 : exactInterval 13 69 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_69 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 69) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_69 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_69 : oddCount 69 13 = 4 ∧ acceleratedOrbit 13 69 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_69 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 69) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_69.1, data_13_69.2]

/-- Complete interval computation for depth 13, residue 70. -/
theorem bounds_13_70 : exactInterval 13 70 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_70 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 70) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_70 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_70 : oddCount 70 13 = 4 ∧ acceleratedOrbit 13 70 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_70 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 70) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_70.1, data_13_70.2]

/-- Complete interval computation for depth 13, residue 71. -/
theorem bounds_13_71 : exactInterval 13 71 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_71 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 71) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_71 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_71 : oddCount 71 13 = 9 ∧ acceleratedOrbit 13 71 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_71 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 71) = 3 ^ 9 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_71.1, data_13_71.2]

/-- Complete interval computation for depth 13, residue 72. -/
theorem bounds_13_72 : exactInterval 13 72 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_72 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 72) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_72 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_72 : oddCount 72 13 = 6 ∧ acceleratedOrbit 13 72 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_72 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 72) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_72.1, data_13_72.2]

/-- Complete interval computation for depth 13, residue 73. -/
theorem bounds_13_73 : exactInterval 13 73 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_73 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 73) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_73 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_73 : oddCount 73 13 = 9 ∧ acceleratedOrbit 13 73 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_73 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 73) = 3 ^ 9 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_73.1, data_13_73.2]

/-- Complete interval computation for depth 13, residue 74. -/
theorem bounds_13_74 : exactInterval 13 74 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_74 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 74) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_74 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_74 : oddCount 74 13 = 6 ∧ acceleratedOrbit 13 74 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_74 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 74) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_74.1, data_13_74.2]

/-- Complete interval computation for depth 13, residue 75. -/
theorem bounds_13_75 : exactInterval 13 75 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_75 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 75) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_75 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_75 : oddCount 75 13 = 4 ∧ acceleratedOrbit 13 75 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_75 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 75) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_75.1, data_13_75.2]

/-- Complete interval computation for depth 13, residue 76. -/
theorem bounds_13_76 : exactInterval 13 76 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_76 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 76) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_76 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_76 : oddCount 76 13 = 6 ∧ acceleratedOrbit 13 76 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_76 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 76) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_76.1, data_13_76.2]

/-- Complete interval computation for depth 13, residue 77. -/
theorem bounds_13_77 : exactInterval 13 77 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_77 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 77) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_77 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_77 : oddCount 77 13 = 6 ∧ acceleratedOrbit 13 77 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_77 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 77) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_77.1, data_13_77.2]

/-- Complete interval computation for depth 13, residue 78. -/
theorem bounds_13_78 : exactInterval 13 78 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_78 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 78) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_78 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_78 : oddCount 78 13 = 7 ∧ acceleratedOrbit 13 78 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_78 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 78) = 3 ^ 7 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_78.1, data_13_78.2]

/-- Complete interval computation for depth 13, residue 79. -/
theorem bounds_13_79 : exactInterval 13 79 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_79 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 79) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_79 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_79 : oddCount 79 13 = 7 ∧ acceleratedOrbit 13 79 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_79 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 79) = 3 ^ 7 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_79.1, data_13_79.2]

/-- Complete interval computation for depth 13, residue 80. -/
theorem bounds_13_80 : exactInterval 13 80 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_80 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 80) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_80 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_80 : oddCount 80 13 = 4 ∧ acceleratedOrbit 13 80 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_80 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 80) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_80.1, data_13_80.2]

end Collatz.Research.StoppingAtlas.Batch0472
