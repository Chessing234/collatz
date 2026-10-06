import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch030

/-- Complete interval computation for depth 8, residue 42. -/
theorem bounds_8_42 : exactInterval 8 42 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_42 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 42) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_42 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_42 : oddCount 42 8 = 2 ∧ acceleratedOrbit 8 42 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_42 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 42) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_42.1, data_8_42.2]

/-- Complete interval computation for depth 8, residue 43. -/
theorem bounds_8_43 : exactInterval 8 43 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_43 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 43) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_43 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_43 : oddCount 43 8 = 4 ∧ acceleratedOrbit 8 43 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_43 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 43) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_43.1, data_8_43.2]

/-- Complete interval computation for depth 8, residue 44. -/
theorem bounds_8_44 : exactInterval 8 44 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_44 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 44) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_44 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_44 : oddCount 44 8 = 3 ∧ acceleratedOrbit 8 44 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_44 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 44) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_44.1, data_8_44.2]

/-- Complete interval computation for depth 8, residue 45. -/
theorem bounds_8_45 : exactInterval 8 45 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_45 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 45) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_45 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_45 : oddCount 45 8 = 3 ∧ acceleratedOrbit 8 45 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_45 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 45) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_45.1, data_8_45.2]

/-- Complete interval computation for depth 8, residue 46. -/
theorem bounds_8_46 : exactInterval 8 46 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_46 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 46) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_46 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_46 : oddCount 46 8 = 3 ∧ acceleratedOrbit 8 46 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_46 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 46) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_46.1, data_8_46.2]

/-- Complete interval computation for depth 8, residue 47. -/
theorem bounds_8_47 : exactInterval 8 47 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_47 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 47) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_47 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_47 : oddCount 47 8 = 6 ∧ acceleratedOrbit 8 47 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_47 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 47) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_47.1, data_8_47.2]

/-- Complete interval computation for depth 8, residue 48. -/
theorem bounds_8_48 : exactInterval 8 48 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_48 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 48) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_48 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_48 : oddCount 48 8 = 2 ∧ acceleratedOrbit 8 48 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_48 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 48) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_48.1, data_8_48.2]

/-- Complete interval computation for depth 8, residue 49. -/
theorem bounds_8_49 : exactInterval 8 49 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_49 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 49) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_49 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_49 : oddCount 49 8 = 4 ∧ acceleratedOrbit 8 49 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_49 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 49) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_49.1, data_8_49.2]

/-- Complete interval computation for depth 8, residue 50. -/
theorem bounds_8_50 : exactInterval 8 50 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_50 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 50) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_50 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_50 : oddCount 50 8 = 4 ∧ acceleratedOrbit 8 50 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_50 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 50) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_50.1, data_8_50.2]

/-- Complete interval computation for depth 8, residue 51. -/
theorem bounds_8_51 : exactInterval 8 51 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_51 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 51) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_51 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_51 : oddCount 51 8 = 4 ∧ acceleratedOrbit 8 51 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_51 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 51) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_51.1, data_8_51.2]

end Collatz.Research.DescentIntervals.Batch030
