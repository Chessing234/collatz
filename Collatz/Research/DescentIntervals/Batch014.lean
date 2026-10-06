import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch014

/-- Complete interval computation for depth 7, residue 6. -/
theorem bounds_7_6 : exactInterval 7 6 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_6 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 6) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_6 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_6 : oddCount 6 7 = 3 ∧ acceleratedOrbit 7 6 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_6 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 6) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_6.1, data_7_6.2]

/-- Complete interval computation for depth 7, residue 7. -/
theorem bounds_7_7 : exactInterval 7 7 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_7 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 7) 7 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_7 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_7 : oddCount 7 7 = 4 ∧ acceleratedOrbit 7 7 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_7 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 7) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_7.1, data_7_7.2]

/-- Complete interval computation for depth 7, residue 8. -/
theorem bounds_7_8 : exactInterval 7 8 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_8 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 8) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_8 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_8 : oddCount 8 7 = 2 ∧ acceleratedOrbit 7 8 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_8 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 8) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_8.1, data_7_8.2]

/-- Complete interval computation for depth 7, residue 9. -/
theorem bounds_7_9 : exactInterval 7 9 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_9 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 9) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_9 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_9 : oddCount 9 7 = 5 ∧ acceleratedOrbit 7 9 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_9 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 9) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_9.1, data_7_9.2]

/-- Complete interval computation for depth 7, residue 10. -/
theorem bounds_7_10 : exactInterval 7 10 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_10 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 10) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_10 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_10 : oddCount 10 7 = 2 ∧ acceleratedOrbit 7 10 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_10 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 10) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_10.1, data_7_10.2]

/-- Complete interval computation for depth 7, residue 11. -/
theorem bounds_7_11 : exactInterval 7 11 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_11 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 11) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_11 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_11 : oddCount 11 7 = 4 ∧ acceleratedOrbit 7 11 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_11 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 11) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_11.1, data_7_11.2]

/-- Complete interval computation for depth 7, residue 12. -/
theorem bounds_7_12 : exactInterval 7 12 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_12 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 12) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_12 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_12 : oddCount 12 7 = 2 ∧ acceleratedOrbit 7 12 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_12 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 12) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_12.1, data_7_12.2]

/-- Complete interval computation for depth 7, residue 13. -/
theorem bounds_7_13 : exactInterval 7 13 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_13 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 13) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_13 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_13 : oddCount 13 7 = 2 ∧ acceleratedOrbit 7 13 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_13 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 13) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_13.1, data_7_13.2]

/-- Complete interval computation for depth 7, residue 14. -/
theorem bounds_7_14 : exactInterval 7 14 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_14 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 14) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_14 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_14 : oddCount 14 7 = 4 ∧ acceleratedOrbit 7 14 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_14 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 14) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_14.1, data_7_14.2]

/-- Complete interval computation for depth 7, residue 15. -/
theorem bounds_7_15 : exactInterval 7 15 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_15 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 15) 7 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_15 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_15 : oddCount 15 7 = 4 ∧ acceleratedOrbit 7 15 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_15 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 15) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_15.1, data_7_15.2]

/-- Complete interval computation for depth 7, residue 16. -/
theorem bounds_7_16 : exactInterval 7 16 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_16 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 16) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_16 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_16 : oddCount 16 7 = 2 ∧ acceleratedOrbit 7 16 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_16 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 16) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_16.1, data_7_16.2]

end Collatz.Research.DescentIntervals.Batch014
