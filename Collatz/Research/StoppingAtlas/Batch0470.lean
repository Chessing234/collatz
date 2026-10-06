import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0470

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 35. -/
theorem bounds_13_35 : exactInterval 13 35 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_35 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 35) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_35 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_35 : oddCount 35 13 = 5 ∧ acceleratedOrbit 13 35 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_35 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 35) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_35.1, data_13_35.2]

/-- Complete interval computation for depth 13, residue 36. -/
theorem bounds_13_36 : exactInterval 13 36 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_36 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 36) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_36 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_36 : oddCount 36 13 = 6 ∧ acceleratedOrbit 13 36 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_36 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 36) = 3 ^ 6 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_36.1, data_13_36.2]

/-- Complete interval computation for depth 13, residue 37. -/
theorem bounds_13_37 : exactInterval 13 37 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_37 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 37) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_37 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_37 : oddCount 37 13 = 6 ∧ acceleratedOrbit 13 37 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_37 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 37) = 3 ^ 6 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_37.1, data_13_37.2]

/-- Complete interval computation for depth 13, residue 38. -/
theorem bounds_13_38 : exactInterval 13 38 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_38 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 38) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_38 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_38 : oddCount 38 13 = 6 ∧ acceleratedOrbit 13 38 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_38 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 38) = 3 ^ 6 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_38.1, data_13_38.2]

/-- Complete interval computation for depth 13, residue 39. -/
theorem bounds_13_39 : exactInterval 13 39 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_39 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 39) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_39 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_39 : oddCount 39 13 = 7 ∧ acceleratedOrbit 13 39 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_39 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 39) = 3 ^ 7 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_39.1, data_13_39.2]

/-- Complete interval computation for depth 13, residue 40. -/
theorem bounds_13_40 : exactInterval 13 40 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_40 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 40) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_40 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_40 : oddCount 40 13 = 4 ∧ acceleratedOrbit 13 40 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_40 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 40) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_40.1, data_13_40.2]

/-- Complete interval computation for depth 13, residue 41. -/
theorem bounds_13_41 : exactInterval 13 41 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_41 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 41) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_41 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_41 : oddCount 41 13 = 9 ∧ acceleratedOrbit 13 41 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_41 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 41) = 3 ^ 9 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_41.1, data_13_41.2]

/-- Complete interval computation for depth 13, residue 42. -/
theorem bounds_13_42 : exactInterval 13 42 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_42 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 42) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_42 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_42 : oddCount 42 13 = 4 ∧ acceleratedOrbit 13 42 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_42 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 42) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_42.1, data_13_42.2]

/-- Complete interval computation for depth 13, residue 43. -/
theorem bounds_13_43 : exactInterval 13 43 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_43 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 43) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_43 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_43 : oddCount 43 13 = 7 ∧ acceleratedOrbit 13 43 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_43 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 43) = 3 ^ 7 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_43.1, data_13_43.2]

/-- Complete interval computation for depth 13, residue 44. -/
theorem bounds_13_44 : exactInterval 13 44 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_44 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 44) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_44 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_44 : oddCount 44 13 = 5 ∧ acceleratedOrbit 13 44 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_44 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 44) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_44.1, data_13_44.2]

/-- Complete interval computation for depth 13, residue 45. -/
theorem bounds_13_45 : exactInterval 13 45 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_45 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 45) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_45 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_45 : oddCount 45 13 = 5 ∧ acceleratedOrbit 13 45 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_45 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 45) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_45.1, data_13_45.2]

/-- Complete interval computation for depth 13, residue 46. -/
theorem bounds_13_46 : exactInterval 13 46 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_46 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 46) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_46 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_46 : oddCount 46 13 = 5 ∧ acceleratedOrbit 13 46 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_46 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 46) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_46.1, data_13_46.2]

/-- Complete interval computation for depth 13, residue 47. -/
theorem bounds_13_47 : exactInterval 13 47 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_47 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 47) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_47 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_47 : oddCount 47 13 = 10 ∧ acceleratedOrbit 13 47 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_47 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 47) = 3 ^ 10 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_47.1, data_13_47.2]

/-- Complete interval computation for depth 13, residue 48. -/
theorem bounds_13_48 : exactInterval 13 48 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_48 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 48) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_48 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_48 : oddCount 48 13 = 4 ∧ acceleratedOrbit 13 48 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_48 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 48) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_48.1, data_13_48.2]

/-- Complete interval computation for depth 13, residue 49. -/
theorem bounds_13_49 : exactInterval 13 49 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_49 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 49) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_49 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_49 : oddCount 49 13 = 6 ∧ acceleratedOrbit 13 49 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_49 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 49) = 3 ^ 6 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_49.1, data_13_49.2]

/-- Complete interval computation for depth 13, residue 50. -/
theorem bounds_13_50 : exactInterval 13 50 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_50 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 50) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_50 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_50 : oddCount 50 13 = 6 ∧ acceleratedOrbit 13 50 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_50 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 50) = 3 ^ 6 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_50.1, data_13_50.2]

end Collatz.Research.StoppingAtlas.Batch0470
