import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch029

/-- Complete interval computation for depth 8, residue 32. -/
theorem bounds_8_32 : exactInterval 8 32 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_32 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 32) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_32 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_32 : oddCount 32 8 = 2 ∧ acceleratedOrbit 8 32 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_32 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 32) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_32.1, data_8_32.2]

/-- Complete interval computation for depth 8, residue 33. -/
theorem bounds_8_33 : exactInterval 8 33 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_33 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 33) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_33 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_33 : oddCount 33 8 = 4 ∧ acceleratedOrbit 8 33 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_33 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 33) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_33.1, data_8_33.2]

/-- Complete interval computation for depth 8, residue 34. -/
theorem bounds_8_34 : exactInterval 8 34 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_34 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 34) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_34 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_34 : oddCount 34 8 = 3 ∧ acceleratedOrbit 8 34 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_34 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 34) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_34.1, data_8_34.2]

/-- Complete interval computation for depth 8, residue 35. -/
theorem bounds_8_35 : exactInterval 8 35 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_35 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 35) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_35 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_35 : oddCount 35 8 = 3 ∧ acceleratedOrbit 8 35 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_35 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 35) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_35.1, data_8_35.2]

/-- Complete interval computation for depth 8, residue 36. -/
theorem bounds_8_36 : exactInterval 8 36 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_36 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 36) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_36 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_36 : oddCount 36 8 = 4 ∧ acceleratedOrbit 8 36 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_36 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 36) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_36.1, data_8_36.2]

/-- Complete interval computation for depth 8, residue 37. -/
theorem bounds_8_37 : exactInterval 8 37 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_37 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 37) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_37 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_37 : oddCount 37 8 = 4 ∧ acceleratedOrbit 8 37 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_37 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 37) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_37.1, data_8_37.2]

/-- Complete interval computation for depth 8, residue 38. -/
theorem bounds_8_38 : exactInterval 8 38 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_38 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 38) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_38 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_38 : oddCount 38 8 = 4 ∧ acceleratedOrbit 8 38 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_38 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 38) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_38.1, data_8_38.2]

/-- Complete interval computation for depth 8, residue 39. -/
theorem bounds_8_39 : exactInterval 8 39 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_39 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 39) 8 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_39 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_39 : oddCount 39 8 = 5 ∧ acceleratedOrbit 8 39 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_39 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 39) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_39.1, data_8_39.2]

/-- Complete interval computation for depth 8, residue 40. -/
theorem bounds_8_40 : exactInterval 8 40 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_40 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 40) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_40 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_40 : oddCount 40 8 = 2 ∧ acceleratedOrbit 8 40 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_40 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 40) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_40.1, data_8_40.2]

/-- Complete interval computation for depth 8, residue 41. -/
theorem bounds_8_41 : exactInterval 8 41 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_41 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 41) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_41 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_41 : oddCount 41 8 = 6 ∧ acceleratedOrbit 8 41 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_41 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 41) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_41.1, data_8_41.2]

end Collatz.Research.DescentIntervals.Batch029
