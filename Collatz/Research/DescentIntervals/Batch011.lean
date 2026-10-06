import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch011

/-- Complete interval computation for depth 6, residue 40. -/
theorem bounds_6_40 : exactInterval 6 40 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_40 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 40) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_40 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_40 : oddCount 40 6 = 1 ∧ acceleratedOrbit 6 40 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_40 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 40) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_40.1, data_6_40.2]

/-- Complete interval computation for depth 6, residue 41. -/
theorem bounds_6_41 : exactInterval 6 41 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_41 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 41) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_41 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_41 : oddCount 41 6 = 5 ∧ acceleratedOrbit 6 41 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_41 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 41) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_41.1, data_6_41.2]

/-- Complete interval computation for depth 6, residue 42. -/
theorem bounds_6_42 : exactInterval 6 42 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_42 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 42) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_42 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_42 : oddCount 42 6 = 1 ∧ acceleratedOrbit 6 42 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_42 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 42) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_42.1, data_6_42.2]

/-- Complete interval computation for depth 6, residue 43. -/
theorem bounds_6_43 : exactInterval 6 43 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_43 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 43) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_43 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_43 : oddCount 43 6 = 4 ∧ acceleratedOrbit 6 43 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_43 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 43) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_43.1, data_6_43.2]

/-- Complete interval computation for depth 6, residue 44. -/
theorem bounds_6_44 : exactInterval 6 44 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_44 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 44) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_44 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_44 : oddCount 44 6 = 3 ∧ acceleratedOrbit 6 44 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_44 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 44) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_44.1, data_6_44.2]

/-- Complete interval computation for depth 6, residue 45. -/
theorem bounds_6_45 : exactInterval 6 45 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_45 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 45) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_45 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_45 : oddCount 45 6 = 3 ∧ acceleratedOrbit 6 45 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_45 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 45) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_45.1, data_6_45.2]

/-- Complete interval computation for depth 6, residue 46. -/
theorem bounds_6_46 : exactInterval 6 46 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_46 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 46) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_46 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_46 : oddCount 46 6 = 3 ∧ acceleratedOrbit 6 46 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_46 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 46) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_46.1, data_6_46.2]

/-- Complete interval computation for depth 6, residue 47. -/
theorem bounds_6_47 : exactInterval 6 47 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_47 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 47) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_47 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_47 : oddCount 47 6 = 5 ∧ acceleratedOrbit 6 47 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_47 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 47) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_47.1, data_6_47.2]

/-- Complete interval computation for depth 6, residue 48. -/
theorem bounds_6_48 : exactInterval 6 48 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_48 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 48) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_48 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_48 : oddCount 48 6 = 2 ∧ acceleratedOrbit 6 48 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_48 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 48) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_48.1, data_6_48.2]

/-- Complete interval computation for depth 6, residue 49. -/
theorem bounds_6_49 : exactInterval 6 49 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_49 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 49) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_49 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_49 : oddCount 49 6 = 2 ∧ acceleratedOrbit 6 49 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_49 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 49) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_49.1, data_6_49.2]

end Collatz.Research.DescentIntervals.Batch011
