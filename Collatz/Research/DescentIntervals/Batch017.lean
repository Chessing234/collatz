import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch017

/-- Complete interval computation for depth 7, residue 37. -/
theorem bounds_7_37 : exactInterval 7 37 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_37 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 37) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_37 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_37 : oddCount 37 7 = 4 ∧ acceleratedOrbit 7 37 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_37 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 37) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_37.1, data_7_37.2]

/-- Complete interval computation for depth 7, residue 38. -/
theorem bounds_7_38 : exactInterval 7 38 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_38 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 38) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_38 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_38 : oddCount 38 7 = 4 ∧ acceleratedOrbit 7 38 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_38 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 38) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_38.1, data_7_38.2]

/-- Complete interval computation for depth 7, residue 39. -/
theorem bounds_7_39 : exactInterval 7 39 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_39 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 39) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_39 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_39 : oddCount 39 7 = 5 ∧ acceleratedOrbit 7 39 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_39 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 39) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_39.1, data_7_39.2]

/-- Complete interval computation for depth 7, residue 40. -/
theorem bounds_7_40 : exactInterval 7 40 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_40 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 40) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_40 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_40 : oddCount 40 7 = 1 ∧ acceleratedOrbit 7 40 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_40 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 40) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_40.1, data_7_40.2]

/-- Complete interval computation for depth 7, residue 41. -/
theorem bounds_7_41 : exactInterval 7 41 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_41 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 41) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_41 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_41 : oddCount 41 7 = 6 ∧ acceleratedOrbit 7 41 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_41 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 41) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_41.1, data_7_41.2]

/-- Complete interval computation for depth 7, residue 42. -/
theorem bounds_7_42 : exactInterval 7 42 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_42 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 42) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_42 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_42 : oddCount 42 7 = 1 ∧ acceleratedOrbit 7 42 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_42 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 42) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_42.1, data_7_42.2]

/-- Complete interval computation for depth 7, residue 43. -/
theorem bounds_7_43 : exactInterval 7 43 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_43 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 43) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_43 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_43 : oddCount 43 7 = 4 ∧ acceleratedOrbit 7 43 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_43 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 43) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_43.1, data_7_43.2]

/-- Complete interval computation for depth 7, residue 44. -/
theorem bounds_7_44 : exactInterval 7 44 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_44 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 44) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_44 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_44 : oddCount 44 7 = 3 ∧ acceleratedOrbit 7 44 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_44 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 44) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_44.1, data_7_44.2]

/-- Complete interval computation for depth 7, residue 45. -/
theorem bounds_7_45 : exactInterval 7 45 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_45 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 45) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_45 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_45 : oddCount 45 7 = 3 ∧ acceleratedOrbit 7 45 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_45 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 45) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_45.1, data_7_45.2]

/-- Complete interval computation for depth 7, residue 46. -/
theorem bounds_7_46 : exactInterval 7 46 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_46 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 46) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_46 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_46 : oddCount 46 7 = 3 ∧ acceleratedOrbit 7 46 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_46 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 46) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_46.1, data_7_46.2]

end Collatz.Research.DescentIntervals.Batch017
