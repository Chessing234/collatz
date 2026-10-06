import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch053

/-- Complete interval computation for depth 9, residue 21. -/
theorem bounds_9_21 : exactInterval 9 21 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_21 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 21) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_21 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_21 : oddCount 21 9 = 3 ∧ acceleratedOrbit 9 21 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_21 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 21) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_21.1, data_9_21.2]

/-- Complete interval computation for depth 9, residue 22. -/
theorem bounds_9_22 : exactInterval 9 22 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_22 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 22) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_22 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_22 : oddCount 22 9 = 4 ∧ acceleratedOrbit 9 22 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_22 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 22) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_22.1, data_9_22.2]

/-- Complete interval computation for depth 9, residue 23. -/
theorem bounds_9_23 : exactInterval 9 23 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_23 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 23) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_23 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_23 : oddCount 23 9 = 4 ∧ acceleratedOrbit 9 23 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_23 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 23) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_23.1, data_9_23.2]

/-- Complete interval computation for depth 9, residue 24. -/
theorem bounds_9_24 : exactInterval 9 24 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_24 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 24) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_24 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_24 : oddCount 24 9 = 3 ∧ acceleratedOrbit 9 24 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_24 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 24) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_24.1, data_9_24.2]

/-- Complete interval computation for depth 9, residue 25. -/
theorem bounds_9_25 : exactInterval 9 25 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_25 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 25) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_25 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_25 : oddCount 25 9 = 5 ∧ acceleratedOrbit 9 25 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_25 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 25) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_25.1, data_9_25.2]

/-- Complete interval computation for depth 9, residue 26. -/
theorem bounds_9_26 : exactInterval 9 26 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_26 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 26) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_26 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_26 : oddCount 26 9 = 3 ∧ acceleratedOrbit 9 26 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_26 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 26) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_26.1, data_9_26.2]

/-- Complete interval computation for depth 9, residue 27. -/
theorem bounds_9_27 : exactInterval 9 27 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_27 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 27) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_27 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_27 : oddCount 27 9 = 7 ∧ acceleratedOrbit 9 27 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_27 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 27) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_27.1, data_9_27.2]

/-- Complete interval computation for depth 9, residue 28. -/
theorem bounds_9_28 : exactInterval 9 28 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_28 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 28) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_28 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_28 : oddCount 28 9 = 4 ∧ acceleratedOrbit 9 28 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_28 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 28) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_28.1, data_9_28.2]

/-- Complete interval computation for depth 9, residue 29. -/
theorem bounds_9_29 : exactInterval 9 29 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_29 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 29) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_29 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_29 : oddCount 29 9 = 4 ∧ acceleratedOrbit 9 29 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_29 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 29) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_29.1, data_9_29.2]

/-- Complete interval computation for depth 9, residue 30. -/
theorem bounds_9_30 : exactInterval 9 30 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_30 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 30) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_30 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_30 : oddCount 30 9 = 4 ∧ acceleratedOrbit 9 30 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_30 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 30) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_30.1, data_9_30.2]

end Collatz.Research.DescentIntervals.Batch053
