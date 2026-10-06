import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch006

/-- Complete interval computation for depth 5, residue 21. -/
theorem bounds_5_21 : exactInterval 5 21 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_21 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 21) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_21 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_21 : oddCount 21 5 = 1 ∧ acceleratedOrbit 5 21 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_21 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 21) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_21.1, data_5_21.2]

/-- Complete interval computation for depth 5, residue 22. -/
theorem bounds_5_22 : exactInterval 5 22 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_22 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 22) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_22 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_22 : oddCount 22 5 = 3 ∧ acceleratedOrbit 5 22 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_22 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 22) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_22.1, data_5_22.2]

/-- Complete interval computation for depth 5, residue 23. -/
theorem bounds_5_23 : exactInterval 5 23 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_23 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 23) 5 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_23 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_23 : oddCount 23 5 = 3 ∧ acceleratedOrbit 5 23 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_23 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 23) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_23.1, data_5_23.2]

/-- Complete interval computation for depth 5, residue 24. -/
theorem bounds_5_24 : exactInterval 5 24 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_24 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 24) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_24 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_24 : oddCount 24 5 = 2 ∧ acceleratedOrbit 5 24 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_24 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 24) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_24.1, data_5_24.2]

/-- Complete interval computation for depth 5, residue 25. -/
theorem bounds_5_25 : exactInterval 5 25 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_25 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 25) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_25 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_25 : oddCount 25 5 = 3 ∧ acceleratedOrbit 5 25 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_25 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 25) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_25.1, data_5_25.2]

/-- Complete interval computation for depth 5, residue 26. -/
theorem bounds_5_26 : exactInterval 5 26 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_26 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 26) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_26 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_26 : oddCount 26 5 = 2 ∧ acceleratedOrbit 5 26 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_26 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 26) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_26.1, data_5_26.2]

/-- Complete interval computation for depth 5, residue 27. -/
theorem bounds_5_27 : exactInterval 5 27 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_27 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 27) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_27 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_27 : oddCount 27 5 = 4 ∧ acceleratedOrbit 5 27 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_27 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 27) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_27.1, data_5_27.2]

/-- Complete interval computation for depth 5, residue 28. -/
theorem bounds_5_28 : exactInterval 5 28 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_28 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 28) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_28 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_28 : oddCount 28 5 = 3 ∧ acceleratedOrbit 5 28 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_28 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 28) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_28.1, data_5_28.2]

/-- Complete interval computation for depth 5, residue 29. -/
theorem bounds_5_29 : exactInterval 5 29 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_29 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 29) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_29 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_29 : oddCount 29 5 = 3 ∧ acceleratedOrbit 5 29 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_29 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 29) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_29.1, data_5_29.2]

/-- Complete interval computation for depth 5, residue 30. -/
theorem bounds_5_30 : exactInterval 5 30 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_30 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 30) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_30 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_30 : oddCount 30 5 = 4 ∧ acceleratedOrbit 5 30 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_30 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 30) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_30.1, data_5_30.2]

end Collatz.Research.DescentIntervals.Batch006
