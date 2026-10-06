import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch054

/-- Complete interval computation for depth 9, residue 31. -/
theorem bounds_9_31 : exactInterval 9 31 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_31 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 31) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_31 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_31 : oddCount 31 9 = 7 ∧ acceleratedOrbit 9 31 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_31 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 31) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_31.1, data_9_31.2]

/-- Complete interval computation for depth 9, residue 32. -/
theorem bounds_9_32 : exactInterval 9 32 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_32 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 32) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_32 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_32 : oddCount 32 9 = 2 ∧ acceleratedOrbit 9 32 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_32 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 32) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_32.1, data_9_32.2]

/-- Complete interval computation for depth 9, residue 33. -/
theorem bounds_9_33 : exactInterval 9 33 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_33 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 33) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_33 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_33 : oddCount 33 9 = 5 ∧ acceleratedOrbit 9 33 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_33 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 33) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_33.1, data_9_33.2]

/-- Complete interval computation for depth 9, residue 34. -/
theorem bounds_9_34 : exactInterval 9 34 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_34 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 34) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_34 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_34 : oddCount 34 9 = 3 ∧ acceleratedOrbit 9 34 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_34 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 34) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_34.1, data_9_34.2]

/-- Complete interval computation for depth 9, residue 35. -/
theorem bounds_9_35 : exactInterval 9 35 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_35 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 35) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_35 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_35 : oddCount 35 9 = 3 ∧ acceleratedOrbit 9 35 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_35 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 35) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_35.1, data_9_35.2]

/-- Complete interval computation for depth 9, residue 36. -/
theorem bounds_9_36 : exactInterval 9 36 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_36 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 36) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_36 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_36 : oddCount 36 9 = 5 ∧ acceleratedOrbit 9 36 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_36 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 36) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_36.1, data_9_36.2]

/-- Complete interval computation for depth 9, residue 37. -/
theorem bounds_9_37 : exactInterval 9 37 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_37 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 37) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_37 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_37 : oddCount 37 9 = 5 ∧ acceleratedOrbit 9 37 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_37 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 37) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_37.1, data_9_37.2]

/-- Complete interval computation for depth 9, residue 38. -/
theorem bounds_9_38 : exactInterval 9 38 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_38 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 38) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_38 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_38 : oddCount 38 9 = 5 ∧ acceleratedOrbit 9 38 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_38 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 38) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_38.1, data_9_38.2]

/-- Complete interval computation for depth 9, residue 39. -/
theorem bounds_9_39 : exactInterval 9 39 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_39 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 39) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_39 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_39 : oddCount 39 9 = 5 ∧ acceleratedOrbit 9 39 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_39 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 39) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_39.1, data_9_39.2]

/-- Complete interval computation for depth 9, residue 40. -/
theorem bounds_9_40 : exactInterval 9 40 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_40 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 40) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_40 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_40 : oddCount 40 9 = 2 ∧ acceleratedOrbit 9 40 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_40 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 40) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_40.1, data_9_40.2]

end Collatz.Research.DescentIntervals.Batch054
