import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0070

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 35. -/
theorem bounds_11_35 : exactInterval 11 35 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_35 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 35) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_35 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_35 : oddCount 35 11 = 4 ∧ acceleratedOrbit 11 35 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_35 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 35) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_35.1, data_11_35.2]

/-- Complete interval computation for depth 11, residue 36. -/
theorem bounds_11_36 : exactInterval 11 36 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_36 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 36) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_36 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_36 : oddCount 36 11 = 5 ∧ acceleratedOrbit 11 36 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_36 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 36) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_36.1, data_11_36.2]

/-- Complete interval computation for depth 11, residue 37. -/
theorem bounds_11_37 : exactInterval 11 37 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_37 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 37) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_37 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_37 : oddCount 37 11 = 5 ∧ acceleratedOrbit 11 37 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_37 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 37) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_37.1, data_11_37.2]

/-- Complete interval computation for depth 11, residue 38. -/
theorem bounds_11_38 : exactInterval 11 38 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_38 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 38) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_38 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_38 : oddCount 38 11 = 5 ∧ acceleratedOrbit 11 38 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_38 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 38) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_38.1, data_11_38.2]

/-- Complete interval computation for depth 11, residue 39. -/
theorem bounds_11_39 : exactInterval 11 39 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_39 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 39) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_39 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_39 : oddCount 39 11 = 7 ∧ acceleratedOrbit 11 39 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_39 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 39) = 3 ^ 7 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_39.1, data_11_39.2]

/-- Complete interval computation for depth 11, residue 40. -/
theorem bounds_11_40 : exactInterval 11 40 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_40 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 40) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_40 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_40 : oddCount 40 11 = 3 ∧ acceleratedOrbit 11 40 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_40 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 40) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_40.1, data_11_40.2]

/-- Complete interval computation for depth 11, residue 41. -/
theorem bounds_11_41 : exactInterval 11 41 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_41 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 41) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_41 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_41 : oddCount 41 11 = 8 ∧ acceleratedOrbit 11 41 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_41 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 41) = 3 ^ 8 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_41.1, data_11_41.2]

/-- Complete interval computation for depth 11, residue 42. -/
theorem bounds_11_42 : exactInterval 11 42 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_42 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 42) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_42 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_42 : oddCount 42 11 = 3 ∧ acceleratedOrbit 11 42 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_42 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 42) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_42.1, data_11_42.2]

/-- Complete interval computation for depth 11, residue 43. -/
theorem bounds_11_43 : exactInterval 11 43 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_43 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 43) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_43 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_43 : oddCount 43 11 = 6 ∧ acceleratedOrbit 11 43 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_43 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 43) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_43.1, data_11_43.2]

/-- Complete interval computation for depth 11, residue 44. -/
theorem bounds_11_44 : exactInterval 11 44 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_44 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 44) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_44 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_44 : oddCount 44 11 = 4 ∧ acceleratedOrbit 11 44 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_44 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 44) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_44.1, data_11_44.2]

/-- Complete interval computation for depth 11, residue 45. -/
theorem bounds_11_45 : exactInterval 11 45 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_45 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 45) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_45 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_45 : oddCount 45 11 = 4 ∧ acceleratedOrbit 11 45 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_45 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 45) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_45.1, data_11_45.2]

/-- Complete interval computation for depth 11, residue 46. -/
theorem bounds_11_46 : exactInterval 11 46 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_46 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 46) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_46 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_46 : oddCount 46 11 = 4 ∧ acceleratedOrbit 11 46 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_46 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 46) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_46.1, data_11_46.2]

/-- Complete interval computation for depth 11, residue 47. -/
theorem bounds_11_47 : exactInterval 11 47 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_47 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 47) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_47 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_47 : oddCount 47 11 = 8 ∧ acceleratedOrbit 11 47 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_47 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 47) = 3 ^ 8 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_47.1, data_11_47.2]

/-- Complete interval computation for depth 11, residue 48. -/
theorem bounds_11_48 : exactInterval 11 48 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_48 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 48) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_48 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_48 : oddCount 48 11 = 3 ∧ acceleratedOrbit 11 48 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_48 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 48) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_48.1, data_11_48.2]

/-- Complete interval computation for depth 11, residue 49. -/
theorem bounds_11_49 : exactInterval 11 49 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_49 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 49) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_49 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_49 : oddCount 49 11 = 6 ∧ acceleratedOrbit 11 49 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_49 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 49) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_49.1, data_11_49.2]

/-- Complete interval computation for depth 11, residue 50. -/
theorem bounds_11_50 : exactInterval 11 50 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_50 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 50) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_50 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_50 : oddCount 50 11 = 6 ∧ acceleratedOrbit 11 50 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_50 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 50) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_50.1, data_11_50.2]

end Collatz.Research.StoppingAtlas.Batch0070
