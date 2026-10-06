import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch008

/-- Complete interval computation for depth 6, residue 9. -/
theorem bounds_6_9 : exactInterval 6 9 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_9 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 9) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_9 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_9 : oddCount 9 6 = 4 ∧ acceleratedOrbit 6 9 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_9 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 9) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_9.1, data_6_9.2]

/-- Complete interval computation for depth 6, residue 10. -/
theorem bounds_6_10 : exactInterval 6 10 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_10 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 10) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_10 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_10 : oddCount 10 6 = 2 ∧ acceleratedOrbit 6 10 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_10 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 10) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_10.1, data_6_10.2]

/-- Complete interval computation for depth 6, residue 11. -/
theorem bounds_6_11 : exactInterval 6 11 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_11 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 11) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_11 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_11 : oddCount 11 6 = 3 ∧ acceleratedOrbit 6 11 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_11 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 11) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_11.1, data_6_11.2]

/-- Complete interval computation for depth 6, residue 12. -/
theorem bounds_6_12 : exactInterval 6 12 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_12 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 12) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_12 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_12 : oddCount 12 6 = 2 ∧ acceleratedOrbit 6 12 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_12 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 12) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_12.1, data_6_12.2]

/-- Complete interval computation for depth 6, residue 13. -/
theorem bounds_6_13 : exactInterval 6 13 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_13 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 13) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_13 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_13 : oddCount 13 6 = 2 ∧ acceleratedOrbit 6 13 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_13 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 13) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_13.1, data_6_13.2]

/-- Complete interval computation for depth 6, residue 14. -/
theorem bounds_6_14 : exactInterval 6 14 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_14 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 14) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_14 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_14 : oddCount 14 6 = 4 ∧ acceleratedOrbit 6 14 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_14 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 14) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_14.1, data_6_14.2]

/-- Complete interval computation for depth 6, residue 15. -/
theorem bounds_6_15 : exactInterval 6 15 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_15 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 15) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_15 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_15 : oddCount 15 6 = 4 ∧ acceleratedOrbit 6 15 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_15 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 15) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_15.1, data_6_15.2]

/-- Complete interval computation for depth 6, residue 16. -/
theorem bounds_6_16 : exactInterval 6 16 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_16 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 16) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_16 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_16 : oddCount 16 6 = 1 ∧ acceleratedOrbit 6 16 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_16 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 16) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_16.1, data_6_16.2]

/-- Complete interval computation for depth 6, residue 17. -/
theorem bounds_6_17 : exactInterval 6 17 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_17 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 17) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_17 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_17 : oddCount 17 6 = 3 ∧ acceleratedOrbit 6 17 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_17 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 17) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_17.1, data_6_17.2]

/-- Complete interval computation for depth 6, residue 18. -/
theorem bounds_6_18 : exactInterval 6 18 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_18 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 18) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_18 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_18 : oddCount 18 6 = 4 ∧ acceleratedOrbit 6 18 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_18 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 18) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_18.1, data_6_18.2]

end Collatz.Research.DescentIntervals.Batch008
