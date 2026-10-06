import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch013

/-- Complete interval computation for depth 6, residue 60. -/
theorem bounds_6_60 : exactInterval 6 60 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_60 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 60) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_60 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_60 : oddCount 60 6 = 4 ∧ acceleratedOrbit 6 60 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_60 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 60) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_60.1, data_6_60.2]

/-- Complete interval computation for depth 6, residue 61. -/
theorem bounds_6_61 : exactInterval 6 61 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_61 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 61) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_61 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_61 : oddCount 61 6 = 4 ∧ acceleratedOrbit 6 61 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_61 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 61) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_61.1, data_6_61.2]

/-- Complete interval computation for depth 6, residue 62. -/
theorem bounds_6_62 : exactInterval 6 62 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_62 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 62) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_62 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_62 : oddCount 62 6 = 5 ∧ acceleratedOrbit 6 62 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_62 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 62) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_62.1, data_6_62.2]

/-- Complete interval computation for depth 6, residue 63. -/
theorem bounds_6_63 : exactInterval 6 63 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_63 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 63) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_63 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_63 : oddCount 63 6 = 6 ∧ acceleratedOrbit 6 63 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_63 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 63) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_63.1, data_6_63.2]

/-- Complete interval computation for depth 7, residue 0. -/
theorem bounds_7_0 : exactInterval 7 0 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_0 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 0) 7 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_0 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_0 : oddCount 0 7 = 0 ∧ acceleratedOrbit 7 0 = 0 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_0 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 0) = 3 ^ 0 * m + 0 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_0.1, data_7_0.2]

/-- Complete interval computation for depth 7, residue 1. -/
theorem bounds_7_1 : exactInterval 7 1 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_1 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 1) 7 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_1 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_1 : oddCount 1 7 = 4 ∧ acceleratedOrbit 7 1 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_1 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 1) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_1.1, data_7_1.2]

/-- Complete interval computation for depth 7, residue 2. -/
theorem bounds_7_2 : exactInterval 7 2 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_2 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 2) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_2 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_2 : oddCount 2 7 = 3 ∧ acceleratedOrbit 7 2 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_2 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 2) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_2.1, data_7_2.2]

/-- Complete interval computation for depth 7, residue 3. -/
theorem bounds_7_3 : exactInterval 7 3 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_3 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 3) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_3 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_3 : oddCount 3 7 = 3 ∧ acceleratedOrbit 7 3 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_3 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 3) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_3.1, data_7_3.2]

/-- Complete interval computation for depth 7, residue 4. -/
theorem bounds_7_4 : exactInterval 7 4 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_4 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 4) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_4 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_4 : oddCount 4 7 = 3 ∧ acceleratedOrbit 7 4 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_4 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 4) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_4.1, data_7_4.2]

/-- Complete interval computation for depth 7, residue 5. -/
theorem bounds_7_5 : exactInterval 7 5 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_5 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 5) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_5 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_5 : oddCount 5 7 = 3 ∧ acceleratedOrbit 7 5 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_5 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 5) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_5.1, data_7_5.2]

end Collatz.Research.DescentIntervals.Batch013
