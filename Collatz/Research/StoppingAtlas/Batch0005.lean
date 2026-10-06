import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0005

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 61. -/
theorem bounds_10_61 : exactInterval 10 61 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_61 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 61) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_61 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_61 : oddCount 61 10 = 4 ∧ acceleratedOrbit 10 61 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_61 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 61) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_61.1, data_10_61.2]

/-- Complete interval computation for depth 10, residue 62. -/
theorem bounds_10_62 : exactInterval 10 62 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_62 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 62) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_62 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_62 : oddCount 62 10 = 7 ∧ acceleratedOrbit 10 62 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_62 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 62) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_62.1, data_10_62.2]

/-- Complete interval computation for depth 10, residue 63. -/
theorem bounds_10_63 : exactInterval 10 63 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_63 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 63) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_63 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_63 : oddCount 63 10 = 7 ∧ acceleratedOrbit 10 63 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_63 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 63) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_63.1, data_10_63.2]

/-- Complete interval computation for depth 10, residue 64. -/
theorem bounds_10_64 : exactInterval 10 64 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_64 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 64) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_64 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_64 : oddCount 64 10 = 2 ∧ acceleratedOrbit 10 64 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_64 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 64) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_64.1, data_10_64.2]

/-- Complete interval computation for depth 10, residue 65. -/
theorem bounds_10_65 : exactInterval 10 65 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_65 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 65) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_65 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_65 : oddCount 65 10 = 5 ∧ acceleratedOrbit 10 65 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_65 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 65) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_65.1, data_10_65.2]

/-- Complete interval computation for depth 10, residue 66. -/
theorem bounds_10_66 : exactInterval 10 66 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_66 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 66) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_66 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_66 : oddCount 66 10 = 5 ∧ acceleratedOrbit 10 66 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_66 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 66) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_66.1, data_10_66.2]

/-- Complete interval computation for depth 10, residue 67. -/
theorem bounds_10_67 : exactInterval 10 67 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_67 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 67) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_67 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_67 : oddCount 67 10 = 5 ∧ acceleratedOrbit 10 67 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_67 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 67) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_67.1, data_10_67.2]

/-- Complete interval computation for depth 10, residue 68. -/
theorem bounds_10_68 : exactInterval 10 68 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_68 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 68) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_68 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_68 : oddCount 68 10 = 3 ∧ acceleratedOrbit 10 68 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_68 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 68) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_68.1, data_10_68.2]

/-- Complete interval computation for depth 10, residue 69. -/
theorem bounds_10_69 : exactInterval 10 69 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_69 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 69) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_69 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_69 : oddCount 69 10 = 3 ∧ acceleratedOrbit 10 69 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_69 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 69) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_69.1, data_10_69.2]

/-- Complete interval computation for depth 10, residue 70. -/
theorem bounds_10_70 : exactInterval 10 70 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_70 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 70) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_70 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_70 : oddCount 70 10 = 3 ∧ acceleratedOrbit 10 70 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_70 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 70) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_70.1, data_10_70.2]

/-- Complete interval computation for depth 10, residue 71. -/
theorem bounds_10_71 : exactInterval 10 71 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_71 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 71) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_71 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_71 : oddCount 71 10 = 7 ∧ acceleratedOrbit 10 71 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_71 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 71) = 3 ^ 7 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_71.1, data_10_71.2]

/-- Complete interval computation for depth 10, residue 72. -/
theorem bounds_10_72 : exactInterval 10 72 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_72 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 72) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_72 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_72 : oddCount 72 10 = 5 ∧ acceleratedOrbit 10 72 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_72 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 72) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_72.1, data_10_72.2]

/-- Complete interval computation for depth 10, residue 73. -/
theorem bounds_10_73 : exactInterval 10 73 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_73 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 73) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_73 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_73 : oddCount 73 10 = 7 ∧ acceleratedOrbit 10 73 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_73 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 73) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_73.1, data_10_73.2]

/-- Complete interval computation for depth 10, residue 74. -/
theorem bounds_10_74 : exactInterval 10 74 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_74 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 74) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_74 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_74 : oddCount 74 10 = 5 ∧ acceleratedOrbit 10 74 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_74 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 74) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_74.1, data_10_74.2]

/-- Complete interval computation for depth 10, residue 75. -/
theorem bounds_10_75 : exactInterval 10 75 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_75 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 75) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_75 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_75 : oddCount 75 10 = 3 ∧ acceleratedOrbit 10 75 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_75 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 75) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_75.1, data_10_75.2]

end Collatz.Research.StoppingAtlas.Batch0005
