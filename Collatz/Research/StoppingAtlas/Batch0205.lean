import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0205

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 61. -/
theorem bounds_12_61 : exactInterval 12 61 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_61 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 61) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_61 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_61 : oddCount 61 12 = 5 ∧ acceleratedOrbit 12 61 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_61 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 61) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_61.1, data_12_61.2]

/-- Complete interval computation for depth 12, residue 62. -/
theorem bounds_12_62 : exactInterval 12 62 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_62 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 62) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_62 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_62 : oddCount 62 12 = 8 ∧ acceleratedOrbit 12 62 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_62 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 62) = 3 ^ 8 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_62.1, data_12_62.2]

/-- Complete interval computation for depth 12, residue 63. -/
theorem bounds_12_63 : exactInterval 12 63 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_63 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 63) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_63 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_63 : oddCount 63 12 = 8 ∧ acceleratedOrbit 12 63 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_63 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 63) = 3 ^ 8 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_63.1, data_12_63.2]

/-- Complete interval computation for depth 12, residue 64. -/
theorem bounds_12_64 : exactInterval 12 64 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_64 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 64) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_64 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_64 : oddCount 64 12 = 3 ∧ acceleratedOrbit 12 64 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_64 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 64) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_64.1, data_12_64.2]

/-- Complete interval computation for depth 12, residue 65. -/
theorem bounds_12_65 : exactInterval 12 65 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_65 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 65) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_65 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_65 : oddCount 65 12 = 6 ∧ acceleratedOrbit 12 65 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_65 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 65) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_65.1, data_12_65.2]

/-- Complete interval computation for depth 12, residue 66. -/
theorem bounds_12_66 : exactInterval 12 66 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_66 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 66) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_66 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_66 : oddCount 66 12 = 6 ∧ acceleratedOrbit 12 66 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_66 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 66) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_66.1, data_12_66.2]

/-- Complete interval computation for depth 12, residue 67. -/
theorem bounds_12_67 : exactInterval 12 67 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_67 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 67) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_67 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_67 : oddCount 67 12 = 6 ∧ acceleratedOrbit 12 67 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_67 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 67) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_67.1, data_12_67.2]

/-- Complete interval computation for depth 12, residue 68. -/
theorem bounds_12_68 : exactInterval 12 68 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_68 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 68) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_68 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_68 : oddCount 68 12 = 4 ∧ acceleratedOrbit 12 68 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_68 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 68) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_68.1, data_12_68.2]

/-- Complete interval computation for depth 12, residue 69. -/
theorem bounds_12_69 : exactInterval 12 69 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_69 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 69) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_69 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_69 : oddCount 69 12 = 4 ∧ acceleratedOrbit 12 69 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_69 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 69) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_69.1, data_12_69.2]

/-- Complete interval computation for depth 12, residue 70. -/
theorem bounds_12_70 : exactInterval 12 70 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_70 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 70) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_70 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_70 : oddCount 70 12 = 4 ∧ acceleratedOrbit 12 70 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_70 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 70) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_70.1, data_12_70.2]

/-- Complete interval computation for depth 12, residue 71. -/
theorem bounds_12_71 : exactInterval 12 71 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_71 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 71) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_71 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_71 : oddCount 71 12 = 9 ∧ acceleratedOrbit 12 71 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_71 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 71) = 3 ^ 9 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_71.1, data_12_71.2]

/-- Complete interval computation for depth 12, residue 72. -/
theorem bounds_12_72 : exactInterval 12 72 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_72 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 72) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_72 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_72 : oddCount 72 12 = 5 ∧ acceleratedOrbit 12 72 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_72 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 72) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_72.1, data_12_72.2]

/-- Complete interval computation for depth 12, residue 73. -/
theorem bounds_12_73 : exactInterval 12 73 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_73 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 73) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_73 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_73 : oddCount 73 12 = 8 ∧ acceleratedOrbit 12 73 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_73 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 73) = 3 ^ 8 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_73.1, data_12_73.2]

/-- Complete interval computation for depth 12, residue 74. -/
theorem bounds_12_74 : exactInterval 12 74 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_74 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 74) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_74 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_74 : oddCount 74 12 = 5 ∧ acceleratedOrbit 12 74 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_74 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 74) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_74.1, data_12_74.2]

/-- Complete interval computation for depth 12, residue 75. -/
theorem bounds_12_75 : exactInterval 12 75 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_75 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 75) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_75 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_75 : oddCount 75 12 = 4 ∧ acceleratedOrbit 12 75 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_75 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 75) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_75.1, data_12_75.2]

end Collatz.Research.StoppingAtlas.Batch0205
