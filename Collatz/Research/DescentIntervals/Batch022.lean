import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch022

/-- Complete interval computation for depth 7, residue 88. -/
theorem bounds_7_88 : exactInterval 7 88 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_88 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 88) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_88 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_88 : oddCount 88 7 = 3 ∧ acceleratedOrbit 7 88 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_88 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 88) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_88.1, data_7_88.2]

/-- Complete interval computation for depth 7, residue 89. -/
theorem bounds_7_89 : exactInterval 7 89 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_89 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 89) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_89 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_89 : oddCount 89 7 = 3 ∧ acceleratedOrbit 7 89 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_89 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 89) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_89.1, data_7_89.2]

/-- Complete interval computation for depth 7, residue 90. -/
theorem bounds_7_90 : exactInterval 7 90 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_90 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 90) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_90 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_90 : oddCount 90 7 = 3 ∧ acceleratedOrbit 7 90 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_90 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 90) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_90.1, data_7_90.2]

/-- Complete interval computation for depth 7, residue 91. -/
theorem bounds_7_91 : exactInterval 7 91 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_91 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 91) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_91 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_91 : oddCount 91 7 = 5 ∧ acceleratedOrbit 7 91 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_91 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 91) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_91.1, data_7_91.2]

/-- Complete interval computation for depth 7, residue 92. -/
theorem bounds_7_92 : exactInterval 7 92 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_92 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 92) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_92 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_92 : oddCount 92 7 = 3 ∧ acceleratedOrbit 7 92 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_92 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 92) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_92.1, data_7_92.2]

/-- Complete interval computation for depth 7, residue 93. -/
theorem bounds_7_93 : exactInterval 7 93 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_93 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 93) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_93 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_93 : oddCount 93 7 = 3 ∧ acceleratedOrbit 7 93 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_93 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 93) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_93.1, data_7_93.2]

/-- Complete interval computation for depth 7, residue 94. -/
theorem bounds_7_94 : exactInterval 7 94 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_94 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 94) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_94 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_94 : oddCount 94 7 = 5 ∧ acceleratedOrbit 7 94 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_94 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 94) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_94.1, data_7_94.2]

/-- Complete interval computation for depth 7, residue 95. -/
theorem bounds_7_95 : exactInterval 7 95 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_95 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 95) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_95 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_95 : oddCount 95 7 = 5 ∧ acceleratedOrbit 7 95 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_95 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 95) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_95.1, data_7_95.2]

/-- Complete interval computation for depth 7, residue 96. -/
theorem bounds_7_96 : exactInterval 7 96 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_96 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 96) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_96 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_96 : oddCount 96 7 = 2 ∧ acceleratedOrbit 7 96 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_96 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 96) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_96.1, data_7_96.2]

/-- Complete interval computation for depth 7, residue 97. -/
theorem bounds_7_97 : exactInterval 7 97 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_97 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 97) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_97 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_97 : oddCount 97 7 = 5 ∧ acceleratedOrbit 7 97 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_97 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 97) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_97.1, data_7_97.2]

end Collatz.Research.DescentIntervals.Batch022
