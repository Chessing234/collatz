import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0003

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 30. -/
theorem bounds_10_30 : exactInterval 10 30 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_30 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 30) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_30 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_30 : oddCount 30 10 = 5 ∧ acceleratedOrbit 10 30 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_30 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 30) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_30.1, data_10_30.2]

/-- Complete interval computation for depth 10, residue 31. -/
theorem bounds_10_31 : exactInterval 10 31 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_31 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 31) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_31 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_31 : oddCount 31 10 = 8 ∧ acceleratedOrbit 10 31 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_31 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 31) = 3 ^ 8 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_31.1, data_10_31.2]

/-- Complete interval computation for depth 10, residue 32. -/
theorem bounds_10_32 : exactInterval 10 32 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_32 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 32) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_32 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_32 : oddCount 32 10 = 3 ∧ acceleratedOrbit 10 32 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_32 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 32) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_32.1, data_10_32.2]

/-- Complete interval computation for depth 10, residue 33. -/
theorem bounds_10_33 : exactInterval 10 33 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_33 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 33) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_33 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_33 : oddCount 33 10 = 6 ∧ acceleratedOrbit 10 33 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_33 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 33) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_33.1, data_10_33.2]

/-- Complete interval computation for depth 10, residue 34. -/
theorem bounds_10_34 : exactInterval 10 34 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_34 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 34) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_34 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_34 : oddCount 34 10 = 3 ∧ acceleratedOrbit 10 34 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_34 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 34) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_34.1, data_10_34.2]

/-- Complete interval computation for depth 10, residue 35. -/
theorem bounds_10_35 : exactInterval 10 35 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_35 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 35) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_35 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_35 : oddCount 35 10 = 3 ∧ acceleratedOrbit 10 35 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_35 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 35) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_35.1, data_10_35.2]

/-- Complete interval computation for depth 10, residue 36. -/
theorem bounds_10_36 : exactInterval 10 36 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_36 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 36) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_36 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_36 : oddCount 36 10 = 5 ∧ acceleratedOrbit 10 36 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_36 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 36) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_36.1, data_10_36.2]

/-- Complete interval computation for depth 10, residue 37. -/
theorem bounds_10_37 : exactInterval 10 37 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_37 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 37) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_37 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_37 : oddCount 37 10 = 5 ∧ acceleratedOrbit 10 37 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_37 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 37) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_37.1, data_10_37.2]

/-- Complete interval computation for depth 10, residue 38. -/
theorem bounds_10_38 : exactInterval 10 38 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_38 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 38) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_38 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_38 : oddCount 38 10 = 5 ∧ acceleratedOrbit 10 38 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_38 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 38) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_38.1, data_10_38.2]

/-- Complete interval computation for depth 10, residue 39. -/
theorem bounds_10_39 : exactInterval 10 39 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_39 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 39) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_39 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_39 : oddCount 39 10 = 6 ∧ acceleratedOrbit 10 39 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_39 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 39) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_39.1, data_10_39.2]

/-- Complete interval computation for depth 10, residue 40. -/
theorem bounds_10_40 : exactInterval 10 40 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_40 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 40) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_40 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_40 : oddCount 40 10 = 3 ∧ acceleratedOrbit 10 40 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_40 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 40) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_40.1, data_10_40.2]

/-- Complete interval computation for depth 10, residue 41. -/
theorem bounds_10_41 : exactInterval 10 41 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_41 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 41) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_41 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_41 : oddCount 41 10 = 7 ∧ acceleratedOrbit 10 41 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_41 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 41) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_41.1, data_10_41.2]

/-- Complete interval computation for depth 10, residue 42. -/
theorem bounds_10_42 : exactInterval 10 42 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_42 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 42) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_42 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_42 : oddCount 42 10 = 3 ∧ acceleratedOrbit 10 42 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_42 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 42) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_42.1, data_10_42.2]

/-- Complete interval computation for depth 10, residue 43. -/
theorem bounds_10_43 : exactInterval 10 43 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_43 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 43) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_43 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_43 : oddCount 43 10 = 5 ∧ acceleratedOrbit 10 43 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_43 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 43) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_43.1, data_10_43.2]

/-- Complete interval computation for depth 10, residue 44. -/
theorem bounds_10_44 : exactInterval 10 44 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_44 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 44) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_44 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_44 : oddCount 44 10 = 4 ∧ acceleratedOrbit 10 44 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_44 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 44) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_44.1, data_10_44.2]

/-- Complete interval computation for depth 10, residue 45. -/
theorem bounds_10_45 : exactInterval 10 45 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_45 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 45) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_45 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_45 : oddCount 45 10 = 4 ∧ acceleratedOrbit 10 45 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_45 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 45) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_45.1, data_10_45.2]

end Collatz.Research.StoppingAtlas.Batch0003
