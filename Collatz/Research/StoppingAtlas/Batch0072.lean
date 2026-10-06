import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0072

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 66. -/
theorem bounds_11_66 : exactInterval 11 66 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_66 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 66) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_66 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_66 : oddCount 66 11 = 6 ∧ acceleratedOrbit 11 66 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_66 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 66) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_66.1, data_11_66.2]

/-- Complete interval computation for depth 11, residue 67. -/
theorem bounds_11_67 : exactInterval 11 67 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_67 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 67) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_67 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_67 : oddCount 67 11 = 6 ∧ acceleratedOrbit 11 67 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_67 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 67) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_67.1, data_11_67.2]

/-- Complete interval computation for depth 11, residue 68. -/
theorem bounds_11_68 : exactInterval 11 68 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_68 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 68) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_68 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_68 : oddCount 68 11 = 3 ∧ acceleratedOrbit 11 68 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_68 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 68) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_68.1, data_11_68.2]

/-- Complete interval computation for depth 11, residue 69. -/
theorem bounds_11_69 : exactInterval 11 69 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_69 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 69) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_69 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_69 : oddCount 69 11 = 3 ∧ acceleratedOrbit 11 69 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_69 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 69) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_69.1, data_11_69.2]

/-- Complete interval computation for depth 11, residue 70. -/
theorem bounds_11_70 : exactInterval 11 70 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_70 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 70) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_70 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_70 : oddCount 70 11 = 3 ∧ acceleratedOrbit 11 70 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_70 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 70) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_70.1, data_11_70.2]

/-- Complete interval computation for depth 11, residue 71. -/
theorem bounds_11_71 : exactInterval 11 71 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_71 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 71) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_71 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_71 : oddCount 71 11 = 8 ∧ acceleratedOrbit 11 71 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_71 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 71) = 3 ^ 8 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_71.1, data_11_71.2]

/-- Complete interval computation for depth 11, residue 72. -/
theorem bounds_11_72 : exactInterval 11 72 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_72 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 72) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_72 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_72 : oddCount 72 11 = 5 ∧ acceleratedOrbit 11 72 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_72 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 72) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_72.1, data_11_72.2]

/-- Complete interval computation for depth 11, residue 73. -/
theorem bounds_11_73 : exactInterval 11 73 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_73 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 73) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_73 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_73 : oddCount 73 11 = 8 ∧ acceleratedOrbit 11 73 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_73 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 73) = 3 ^ 8 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_73.1, data_11_73.2]

/-- Complete interval computation for depth 11, residue 74. -/
theorem bounds_11_74 : exactInterval 11 74 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_74 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 74) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_74 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_74 : oddCount 74 11 = 5 ∧ acceleratedOrbit 11 74 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_74 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 74) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_74.1, data_11_74.2]

/-- Complete interval computation for depth 11, residue 75. -/
theorem bounds_11_75 : exactInterval 11 75 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_75 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 75) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_75 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_75 : oddCount 75 11 = 3 ∧ acceleratedOrbit 11 75 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_75 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 75) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_75.1, data_11_75.2]

/-- Complete interval computation for depth 11, residue 76. -/
theorem bounds_11_76 : exactInterval 11 76 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_76 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 76) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_76 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_76 : oddCount 76 11 = 5 ∧ acceleratedOrbit 11 76 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_76 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 76) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_76.1, data_11_76.2]

/-- Complete interval computation for depth 11, residue 77. -/
theorem bounds_11_77 : exactInterval 11 77 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_77 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 77) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_77 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_77 : oddCount 77 11 = 5 ∧ acceleratedOrbit 11 77 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_77 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 77) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_77.1, data_11_77.2]

/-- Complete interval computation for depth 11, residue 78. -/
theorem bounds_11_78 : exactInterval 11 78 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_78 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 78) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_78 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_78 : oddCount 78 11 = 6 ∧ acceleratedOrbit 11 78 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_78 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 78) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_78.1, data_11_78.2]

/-- Complete interval computation for depth 11, residue 79. -/
theorem bounds_11_79 : exactInterval 11 79 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_79 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 79) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_79 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_79 : oddCount 79 11 = 6 ∧ acceleratedOrbit 11 79 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_79 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 79) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_79.1, data_11_79.2]

/-- Complete interval computation for depth 11, residue 80. -/
theorem bounds_11_80 : exactInterval 11 80 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_80 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 80) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_80 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_80 : oddCount 80 11 = 3 ∧ acceleratedOrbit 11 80 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_80 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 80) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_80.1, data_11_80.2]

end Collatz.Research.StoppingAtlas.Batch0072
