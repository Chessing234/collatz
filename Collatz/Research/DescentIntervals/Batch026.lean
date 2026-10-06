import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch026

/-- Complete interval computation for depth 8, residue 1. -/
theorem bounds_8_1 : exactInterval 8 1 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_1 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 1) 8 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_1 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_1 : oddCount 1 8 = 4 ∧ acceleratedOrbit 8 1 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_1 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 1) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_1.1, data_8_1.2]

/-- Complete interval computation for depth 8, residue 2. -/
theorem bounds_8_2 : exactInterval 8 2 = ⟨1, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_2 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 2) 8 ↔ 1 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_2 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_2 : oddCount 2 8 = 4 ∧ acceleratedOrbit 8 2 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_2 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 2) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_2.1, data_8_2.2]

/-- Complete interval computation for depth 8, residue 3. -/
theorem bounds_8_3 : exactInterval 8 3 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_3 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 3) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_3 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_3 : oddCount 3 8 = 4 ∧ acceleratedOrbit 8 3 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_3 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 3) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_3.1, data_8_3.2]

/-- Complete interval computation for depth 8, residue 4. -/
theorem bounds_8_4 : exactInterval 8 4 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_4 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 4) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_4 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_4 : oddCount 4 8 = 3 ∧ acceleratedOrbit 8 4 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_4 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 4) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_4.1, data_8_4.2]

/-- Complete interval computation for depth 8, residue 5. -/
theorem bounds_8_5 : exactInterval 8 5 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_5 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 5) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_5 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_5 : oddCount 5 8 = 3 ∧ acceleratedOrbit 8 5 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_5 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 5) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_5.1, data_8_5.2]

/-- Complete interval computation for depth 8, residue 6. -/
theorem bounds_8_6 : exactInterval 8 6 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_6 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 6) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_6 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_6 : oddCount 6 8 = 3 ∧ acceleratedOrbit 8 6 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_6 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 6) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_6.1, data_8_6.2]

/-- Complete interval computation for depth 8, residue 7. -/
theorem bounds_8_7 : exactInterval 8 7 = ⟨1, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_7 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 7) 8 ↔ 1 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_7 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_7 : oddCount 7 8 = 5 ∧ acceleratedOrbit 8 7 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_7 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 7) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_7.1, data_8_7.2]

/-- Complete interval computation for depth 8, residue 8. -/
theorem bounds_8_8 : exactInterval 8 8 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_8 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 8) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_8 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_8 : oddCount 8 8 = 3 ∧ acceleratedOrbit 8 8 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_8 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 8) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_8.1, data_8_8.2]

/-- Complete interval computation for depth 8, residue 9. -/
theorem bounds_8_9 : exactInterval 8 9 = ⟨1, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_9 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 9) 8 ↔ 1 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_9 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_9 : oddCount 9 8 = 5 ∧ acceleratedOrbit 8 9 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_9 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 9) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_9.1, data_8_9.2]

/-- Complete interval computation for depth 8, residue 10. -/
theorem bounds_8_10 : exactInterval 8 10 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_10 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 10) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_10 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_10 : oddCount 10 8 = 3 ∧ acceleratedOrbit 8 10 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_10 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 10) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_10.1, data_8_10.2]

end Collatz.Research.DescentIntervals.Batch026
