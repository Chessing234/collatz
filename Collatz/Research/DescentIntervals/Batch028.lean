import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch028

/-- Complete interval computation for depth 8, residue 21. -/
theorem bounds_8_21 : exactInterval 8 21 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_21 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 21) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_21 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_21 : oddCount 21 8 = 2 ∧ acceleratedOrbit 8 21 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_21 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 21) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_21.1, data_8_21.2]

/-- Complete interval computation for depth 8, residue 22. -/
theorem bounds_8_22 : exactInterval 8 22 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_22 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 22) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_22 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_22 : oddCount 22 8 = 4 ∧ acceleratedOrbit 8 22 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_22 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 22) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_22.1, data_8_22.2]

/-- Complete interval computation for depth 8, residue 23. -/
theorem bounds_8_23 : exactInterval 8 23 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_23 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 23) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_23 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_23 : oddCount 23 8 = 4 ∧ acceleratedOrbit 8 23 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_23 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 23) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_23.1, data_8_23.2]

/-- Complete interval computation for depth 8, residue 24. -/
theorem bounds_8_24 : exactInterval 8 24 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_24 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 24) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_24 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_24 : oddCount 24 8 = 2 ∧ acceleratedOrbit 8 24 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_24 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 24) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_24.1, data_8_24.2]

/-- Complete interval computation for depth 8, residue 25. -/
theorem bounds_8_25 : exactInterval 8 25 = ⟨1, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_25 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 25) 8 ↔ 1 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_25 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_25 : oddCount 25 8 = 5 ∧ acceleratedOrbit 8 25 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_25 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 25) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_25.1, data_8_25.2]

/-- Complete interval computation for depth 8, residue 26. -/
theorem bounds_8_26 : exactInterval 8 26 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_26 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 26) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_26 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_26 : oddCount 26 8 = 2 ∧ acceleratedOrbit 8 26 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_26 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 26) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_26.1, data_8_26.2]

/-- Complete interval computation for depth 8, residue 27. -/
theorem bounds_8_27 : exactInterval 8 27 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_27 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 27) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_27 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_27 : oddCount 27 8 = 7 ∧ acceleratedOrbit 8 27 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_27 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 27) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_27.1, data_8_27.2]

/-- Complete interval computation for depth 8, residue 28. -/
theorem bounds_8_28 : exactInterval 8 28 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_28 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 28) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_28 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_28 : oddCount 28 8 = 4 ∧ acceleratedOrbit 8 28 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_28 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 28) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_28.1, data_8_28.2]

/-- Complete interval computation for depth 8, residue 29. -/
theorem bounds_8_29 : exactInterval 8 29 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_29 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 29) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_29 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_29 : oddCount 29 8 = 4 ∧ acceleratedOrbit 8 29 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_29 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 29) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_29.1, data_8_29.2]

/-- Complete interval computation for depth 8, residue 30. -/
theorem bounds_8_30 : exactInterval 8 30 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_30 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 30) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_30 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_30 : oddCount 30 8 = 4 ∧ acceleratedOrbit 8 30 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_30 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 30) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_30.1, data_8_30.2]

/-- Complete interval computation for depth 8, residue 31. -/
theorem bounds_8_31 : exactInterval 8 31 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_31 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 31) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_31 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_31 : oddCount 31 8 = 6 ∧ acceleratedOrbit 8 31 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_31 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 31) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_31.1, data_8_31.2]

end Collatz.Research.DescentIntervals.Batch028
