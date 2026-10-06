import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch052

/-- Complete interval computation for depth 9, residue 11. -/
theorem bounds_9_11 : exactInterval 9 11 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_11 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 11) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_11 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_11 : oddCount 11 9 = 4 ∧ acceleratedOrbit 9 11 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_11 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 11) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_11.1, data_9_11.2]

/-- Complete interval computation for depth 9, residue 12. -/
theorem bounds_9_12 : exactInterval 9 12 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_12 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 12) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_12 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_12 : oddCount 12 9 = 3 ∧ acceleratedOrbit 9 12 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_12 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 12) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_12.1, data_9_12.2]

/-- Complete interval computation for depth 9, residue 13. -/
theorem bounds_9_13 : exactInterval 9 13 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_13 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 13) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_13 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_13 : oddCount 13 9 = 3 ∧ acceleratedOrbit 9 13 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_13 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 13) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_13.1, data_9_13.2]

/-- Complete interval computation for depth 9, residue 14. -/
theorem bounds_9_14 : exactInterval 9 14 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_14 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 14) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_14 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_14 : oddCount 14 9 = 5 ∧ acceleratedOrbit 9 14 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_14 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 14) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_14.1, data_9_14.2]

/-- Complete interval computation for depth 9, residue 15. -/
theorem bounds_9_15 : exactInterval 9 15 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_15 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 15) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_15 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_15 : oddCount 15 9 = 5 ∧ acceleratedOrbit 9 15 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_15 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 15) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_15.1, data_9_15.2]

/-- Complete interval computation for depth 9, residue 16. -/
theorem bounds_9_16 : exactInterval 9 16 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_16 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 16) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_16 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_16 : oddCount 16 9 = 3 ∧ acceleratedOrbit 9 16 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_16 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 16) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_16.1, data_9_16.2]

/-- Complete interval computation for depth 9, residue 17. -/
theorem bounds_9_17 : exactInterval 9 17 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_17 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 17) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_17 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_17 : oddCount 17 9 = 3 ∧ acceleratedOrbit 9 17 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_17 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 17) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_17.1, data_9_17.2]

/-- Complete interval computation for depth 9, residue 18. -/
theorem bounds_9_18 : exactInterval 9 18 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_18 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 18) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_18 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_18 : oddCount 18 9 = 5 ∧ acceleratedOrbit 9 18 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_18 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 18) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_18.1, data_9_18.2]

/-- Complete interval computation for depth 9, residue 19. -/
theorem bounds_9_19 : exactInterval 9 19 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_19 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 19) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_19 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_19 : oddCount 19 9 = 5 ∧ acceleratedOrbit 9 19 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_19 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 19) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_19.1, data_9_19.2]

/-- Complete interval computation for depth 9, residue 20. -/
theorem bounds_9_20 : exactInterval 9 20 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_20 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 20) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_20 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_20 : oddCount 20 9 = 3 ∧ acceleratedOrbit 9 20 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_20 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 20) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_20.1, data_9_20.2]

end Collatz.Research.DescentIntervals.Batch052
