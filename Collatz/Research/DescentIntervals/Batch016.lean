import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch016

/-- Complete interval computation for depth 7, residue 27. -/
theorem bounds_7_27 : exactInterval 7 27 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_27 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 27) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_27 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_27 : oddCount 27 7 = 6 ∧ acceleratedOrbit 7 27 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_27 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 27) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_27.1, data_7_27.2]

/-- Complete interval computation for depth 7, residue 28. -/
theorem bounds_7_28 : exactInterval 7 28 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_28 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 28) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_28 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_28 : oddCount 28 7 = 4 ∧ acceleratedOrbit 7 28 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_28 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 28) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_28.1, data_7_28.2]

/-- Complete interval computation for depth 7, residue 29. -/
theorem bounds_7_29 : exactInterval 7 29 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_29 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 29) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_29 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_29 : oddCount 29 7 = 4 ∧ acceleratedOrbit 7 29 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_29 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 29) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_29.1, data_7_29.2]

/-- Complete interval computation for depth 7, residue 30. -/
theorem bounds_7_30 : exactInterval 7 30 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_30 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 30) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_30 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_30 : oddCount 30 7 = 4 ∧ acceleratedOrbit 7 30 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_30 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 30) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_30.1, data_7_30.2]

/-- Complete interval computation for depth 7, residue 31. -/
theorem bounds_7_31 : exactInterval 7 31 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_31 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 31) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_31 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_31 : oddCount 31 7 = 6 ∧ acceleratedOrbit 7 31 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_31 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 31) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_31.1, data_7_31.2]

/-- Complete interval computation for depth 7, residue 32. -/
theorem bounds_7_32 : exactInterval 7 32 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_32 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 32) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_32 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_32 : oddCount 32 7 = 1 ∧ acceleratedOrbit 7 32 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_32 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 32) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_32.1, data_7_32.2]

/-- Complete interval computation for depth 7, residue 33. -/
theorem bounds_7_33 : exactInterval 7 33 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_33 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 33) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_33 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_33 : oddCount 33 7 = 4 ∧ acceleratedOrbit 7 33 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_33 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 33) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_33.1, data_7_33.2]

/-- Complete interval computation for depth 7, residue 34. -/
theorem bounds_7_34 : exactInterval 7 34 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_34 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 34) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_34 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_34 : oddCount 34 7 = 3 ∧ acceleratedOrbit 7 34 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_34 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 34) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_34.1, data_7_34.2]

/-- Complete interval computation for depth 7, residue 35. -/
theorem bounds_7_35 : exactInterval 7 35 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_35 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 35) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_35 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_35 : oddCount 35 7 = 3 ∧ acceleratedOrbit 7 35 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_35 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 35) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_35.1, data_7_35.2]

/-- Complete interval computation for depth 7, residue 36. -/
theorem bounds_7_36 : exactInterval 7 36 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_36 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 36) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_36 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_36 : oddCount 36 7 = 4 ∧ acceleratedOrbit 7 36 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_36 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 36) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_36.1, data_7_36.2]

end Collatz.Research.DescentIntervals.Batch016
