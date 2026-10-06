import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch051

/-- Complete interval computation for depth 9, residue 1. -/
theorem bounds_9_1 : exactInterval 9 1 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_1 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 1) 9 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_1 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_1 : oddCount 1 9 = 5 ∧ acceleratedOrbit 9 1 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_1 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 1) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_1.1, data_9_1.2]

/-- Complete interval computation for depth 9, residue 2. -/
theorem bounds_9_2 : exactInterval 9 2 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_2 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 2) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_2 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_2 : oddCount 2 9 = 4 ∧ acceleratedOrbit 9 2 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_2 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 2) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_2.1, data_9_2.2]

/-- Complete interval computation for depth 9, residue 3. -/
theorem bounds_9_3 : exactInterval 9 3 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_3 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 3) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_3 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_3 : oddCount 3 9 = 4 ∧ acceleratedOrbit 9 3 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_3 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 3) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_3.1, data_9_3.2]

/-- Complete interval computation for depth 9, residue 4. -/
theorem bounds_9_4 : exactInterval 9 4 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_4 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 4) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_4 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_4 : oddCount 4 9 = 4 ∧ acceleratedOrbit 9 4 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_4 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 4) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_4.1, data_9_4.2]

/-- Complete interval computation for depth 9, residue 5. -/
theorem bounds_9_5 : exactInterval 9 5 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_5 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 5) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_5 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_5 : oddCount 5 9 = 4 ∧ acceleratedOrbit 9 5 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_5 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 5) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_5.1, data_9_5.2]

/-- Complete interval computation for depth 9, residue 6. -/
theorem bounds_9_6 : exactInterval 9 6 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_6 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 6) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_6 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_6 : oddCount 6 9 = 4 ∧ acceleratedOrbit 9 6 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_6 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 6) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_6.1, data_9_6.2]

/-- Complete interval computation for depth 9, residue 7. -/
theorem bounds_9_7 : exactInterval 9 7 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_7 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 7) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_7 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_7 : oddCount 7 9 = 5 ∧ acceleratedOrbit 9 7 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_7 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 7) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_7.1, data_9_7.2]

/-- Complete interval computation for depth 9, residue 8. -/
theorem bounds_9_8 : exactInterval 9 8 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_8 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 8) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_8 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_8 : oddCount 8 9 = 3 ∧ acceleratedOrbit 9 8 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_8 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 8) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_8.1, data_9_8.2]

/-- Complete interval computation for depth 9, residue 9. -/
theorem bounds_9_9 : exactInterval 9 9 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_9 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 9) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_9 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_9 : oddCount 9 9 = 5 ∧ acceleratedOrbit 9 9 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_9 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 9) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_9.1, data_9_9.2]

/-- Complete interval computation for depth 9, residue 10. -/
theorem bounds_9_10 : exactInterval 9 10 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_10 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 10) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_10 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_10 : oddCount 10 9 = 3 ∧ acceleratedOrbit 9 10 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_10 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 10) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_10.1, data_9_10.2]

end Collatz.Research.DescentIntervals.Batch051
