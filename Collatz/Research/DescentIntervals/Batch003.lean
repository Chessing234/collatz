import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch003

/-- Complete interval computation for depth 4, residue 6. -/
theorem bounds_4_6 : exactInterval 4 6 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_4_6 (m : Nat) :
    stoppingTime (2 ^ 4 * m + 6) 4 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_4_6 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_4_6 : oddCount 6 4 = 2 ∧ acceleratedOrbit 4 6 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_4_6 (m : Nat) :
    acceleratedOrbit 4 (2 ^ 4 * m + 6) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_4_6.1, data_4_6.2]

/-- Complete interval computation for depth 4, residue 7. -/
theorem bounds_4_7 : exactInterval 4 7 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_4_7 (m : Nat) :
    stoppingTime (2 ^ 4 * m + 7) 4 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_4_7 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_4_7 : oddCount 7 4 = 3 ∧ acceleratedOrbit 4 7 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_4_7 (m : Nat) :
    acceleratedOrbit 4 (2 ^ 4 * m + 7) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_4_7.1, data_4_7.2]

/-- Complete interval computation for depth 4, residue 8. -/
theorem bounds_4_8 : exactInterval 4 8 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_4_8 (m : Nat) :
    stoppingTime (2 ^ 4 * m + 8) 4 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_4_8 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_4_8 : oddCount 8 4 = 1 ∧ acceleratedOrbit 4 8 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_4_8 (m : Nat) :
    acceleratedOrbit 4 (2 ^ 4 * m + 8) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_4_8.1, data_4_8.2]

/-- Complete interval computation for depth 4, residue 9. -/
theorem bounds_4_9 : exactInterval 4 9 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_4_9 (m : Nat) :
    stoppingTime (2 ^ 4 * m + 9) 4 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_4_9 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_4_9 : oddCount 9 4 = 3 ∧ acceleratedOrbit 4 9 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_4_9 (m : Nat) :
    acceleratedOrbit 4 (2 ^ 4 * m + 9) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_4_9.1, data_4_9.2]

/-- Complete interval computation for depth 4, residue 10. -/
theorem bounds_4_10 : exactInterval 4 10 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_4_10 (m : Nat) :
    stoppingTime (2 ^ 4 * m + 10) 4 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_4_10 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_4_10 : oddCount 10 4 = 1 ∧ acceleratedOrbit 4 10 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_4_10 (m : Nat) :
    acceleratedOrbit 4 (2 ^ 4 * m + 10) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_4_10.1, data_4_10.2]

/-- Complete interval computation for depth 4, residue 11. -/
theorem bounds_4_11 : exactInterval 4 11 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_4_11 (m : Nat) :
    stoppingTime (2 ^ 4 * m + 11) 4 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_4_11 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_4_11 : oddCount 11 4 = 3 ∧ acceleratedOrbit 4 11 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_4_11 (m : Nat) :
    acceleratedOrbit 4 (2 ^ 4 * m + 11) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_4_11.1, data_4_11.2]

/-- Complete interval computation for depth 4, residue 12. -/
theorem bounds_4_12 : exactInterval 4 12 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_4_12 (m : Nat) :
    stoppingTime (2 ^ 4 * m + 12) 4 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_4_12 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_4_12 : oddCount 12 4 = 2 ∧ acceleratedOrbit 4 12 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_4_12 (m : Nat) :
    acceleratedOrbit 4 (2 ^ 4 * m + 12) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_4_12.1, data_4_12.2]

/-- Complete interval computation for depth 4, residue 13. -/
theorem bounds_4_13 : exactInterval 4 13 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_4_13 (m : Nat) :
    stoppingTime (2 ^ 4 * m + 13) 4 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_4_13 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_4_13 : oddCount 13 4 = 2 ∧ acceleratedOrbit 4 13 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_4_13 (m : Nat) :
    acceleratedOrbit 4 (2 ^ 4 * m + 13) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_4_13.1, data_4_13.2]

/-- Complete interval computation for depth 4, residue 14. -/
theorem bounds_4_14 : exactInterval 4 14 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_4_14 (m : Nat) :
    stoppingTime (2 ^ 4 * m + 14) 4 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_4_14 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_4_14 : oddCount 14 4 = 3 ∧ acceleratedOrbit 4 14 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_4_14 (m : Nat) :
    acceleratedOrbit 4 (2 ^ 4 * m + 14) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_4_14.1, data_4_14.2]

/-- Complete interval computation for depth 4, residue 15. -/
theorem bounds_4_15 : exactInterval 4 15 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_4_15 (m : Nat) :
    stoppingTime (2 ^ 4 * m + 15) 4 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_4_15 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_4_15 : oddCount 15 4 = 4 ∧ acceleratedOrbit 4 15 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_4_15 (m : Nat) :
    acceleratedOrbit 4 (2 ^ 4 * m + 15) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_4_15.1, data_4_15.2]

end Collatz.Research.DescentIntervals.Batch003
