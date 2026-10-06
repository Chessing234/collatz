import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch010

/-- Complete interval computation for depth 6, residue 29. -/
theorem bounds_6_29 : exactInterval 6 29 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_29 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 29) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_29 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_29 : oddCount 29 6 = 3 ∧ acceleratedOrbit 6 29 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_29 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 29) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_29.1, data_6_29.2]

/-- Complete interval computation for depth 6, residue 30. -/
theorem bounds_6_30 : exactInterval 6 30 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_30 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 30) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_30 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_30 : oddCount 30 6 = 4 ∧ acceleratedOrbit 6 30 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_30 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 30) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_30.1, data_6_30.2]

/-- Complete interval computation for depth 6, residue 31. -/
theorem bounds_6_31 : exactInterval 6 31 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_31 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 31) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_31 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_31 : oddCount 31 6 = 5 ∧ acceleratedOrbit 6 31 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_31 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 31) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_31.1, data_6_31.2]

/-- Complete interval computation for depth 6, residue 32. -/
theorem bounds_6_32 : exactInterval 6 32 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_32 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 32) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_32 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_32 : oddCount 32 6 = 1 ∧ acceleratedOrbit 6 32 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_32 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 32) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_32.1, data_6_32.2]

/-- Complete interval computation for depth 6, residue 33. -/
theorem bounds_6_33 : exactInterval 6 33 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_33 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 33) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_33 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_33 : oddCount 33 6 = 4 ∧ acceleratedOrbit 6 33 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_33 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 33) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_33.1, data_6_33.2]

/-- Complete interval computation for depth 6, residue 34. -/
theorem bounds_6_34 : exactInterval 6 34 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_34 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 34) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_34 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_34 : oddCount 34 6 = 2 ∧ acceleratedOrbit 6 34 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_34 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 34) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_34.1, data_6_34.2]

/-- Complete interval computation for depth 6, residue 35. -/
theorem bounds_6_35 : exactInterval 6 35 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_35 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 35) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_35 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_35 : oddCount 35 6 = 2 ∧ acceleratedOrbit 6 35 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_35 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 35) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_35.1, data_6_35.2]

/-- Complete interval computation for depth 6, residue 36. -/
theorem bounds_6_36 : exactInterval 6 36 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_36 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 36) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_36 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_36 : oddCount 36 6 = 3 ∧ acceleratedOrbit 6 36 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_36 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 36) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_36.1, data_6_36.2]

/-- Complete interval computation for depth 6, residue 37. -/
theorem bounds_6_37 : exactInterval 6 37 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_37 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 37) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_37 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_37 : oddCount 37 6 = 3 ∧ acceleratedOrbit 6 37 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_37 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 37) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_37.1, data_6_37.2]

/-- Complete interval computation for depth 6, residue 38. -/
theorem bounds_6_38 : exactInterval 6 38 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_38 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 38) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_38 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_38 : oddCount 38 6 = 3 ∧ acceleratedOrbit 6 38 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_38 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 38) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_38.1, data_6_38.2]

/-- Complete interval computation for depth 6, residue 39. -/
theorem bounds_6_39 : exactInterval 6 39 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_39 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 39) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_39 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_39 : oddCount 39 6 = 5 ∧ acceleratedOrbit 6 39 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_39 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 39) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_39.1, data_6_39.2]

end Collatz.Research.DescentIntervals.Batch010
