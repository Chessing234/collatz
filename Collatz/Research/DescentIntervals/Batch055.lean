import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch055

/-- Complete interval computation for depth 9, residue 41. -/
theorem bounds_9_41 : exactInterval 9 41 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_41 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 41) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_41 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_41 : oddCount 41 9 = 7 ∧ acceleratedOrbit 9 41 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_41 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 41) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_41.1, data_9_41.2]

/-- Complete interval computation for depth 9, residue 42. -/
theorem bounds_9_42 : exactInterval 9 42 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_42 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 42) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_42 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_42 : oddCount 42 9 = 2 ∧ acceleratedOrbit 9 42 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_42 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 42) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_42.1, data_9_42.2]

/-- Complete interval computation for depth 9, residue 43. -/
theorem bounds_9_43 : exactInterval 9 43 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_43 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 43) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_43 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_43 : oddCount 43 9 = 4 ∧ acceleratedOrbit 9 43 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_43 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 43) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_43.1, data_9_43.2]

/-- Complete interval computation for depth 9, residue 44. -/
theorem bounds_9_44 : exactInterval 9 44 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_44 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 44) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_44 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_44 : oddCount 44 9 = 4 ∧ acceleratedOrbit 9 44 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_44 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 44) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_44.1, data_9_44.2]

/-- Complete interval computation for depth 9, residue 45. -/
theorem bounds_9_45 : exactInterval 9 45 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_45 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 45) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_45 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_45 : oddCount 45 9 = 4 ∧ acceleratedOrbit 9 45 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_45 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 45) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_45.1, data_9_45.2]

/-- Complete interval computation for depth 9, residue 46. -/
theorem bounds_9_46 : exactInterval 9 46 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_46 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 46) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_46 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_46 : oddCount 46 9 = 4 ∧ acceleratedOrbit 9 46 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_46 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 46) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_46.1, data_9_46.2]

/-- Complete interval computation for depth 9, residue 47. -/
theorem bounds_9_47 : exactInterval 9 47 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_47 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 47) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_47 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_47 : oddCount 47 9 = 7 ∧ acceleratedOrbit 9 47 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_47 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 47) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_47.1, data_9_47.2]

/-- Complete interval computation for depth 9, residue 48. -/
theorem bounds_9_48 : exactInterval 9 48 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_48 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 48) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_48 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_48 : oddCount 48 9 = 2 ∧ acceleratedOrbit 9 48 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_48 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 48) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_48.1, data_9_48.2]

/-- Complete interval computation for depth 9, residue 49. -/
theorem bounds_9_49 : exactInterval 9 49 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_49 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 49) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_49 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_49 : oddCount 49 9 = 5 ∧ acceleratedOrbit 9 49 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_49 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 49) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_49.1, data_9_49.2]

/-- Complete interval computation for depth 9, residue 50. -/
theorem bounds_9_50 : exactInterval 9 50 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_50 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 50) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_50 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_50 : oddCount 50 9 = 5 ∧ acceleratedOrbit 9 50 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_50 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 50) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_50.1, data_9_50.2]

/-- Complete interval computation for depth 9, residue 51. -/
theorem bounds_9_51 : exactInterval 9 51 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_51 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 51) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_51 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_51 : oddCount 51 9 = 5 ∧ acceleratedOrbit 9 51 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_51 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 51) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_51.1, data_9_51.2]

end Collatz.Research.DescentIntervals.Batch055
