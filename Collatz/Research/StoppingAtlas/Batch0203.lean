import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0203

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 30. -/
theorem bounds_12_30 : exactInterval 12 30 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_30 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 30) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_30 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_30 : oddCount 30 12 = 5 ∧ acceleratedOrbit 12 30 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_30 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 30) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_30.1, data_12_30.2]

/-- Complete interval computation for depth 12, residue 31. -/
theorem bounds_12_31 : exactInterval 12 31 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_31 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 31) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_31 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_31 : oddCount 31 12 = 9 ∧ acceleratedOrbit 12 31 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_31 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 31) = 3 ^ 9 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_31.1, data_12_31.2]

/-- Complete interval computation for depth 12, residue 32. -/
theorem bounds_12_32 : exactInterval 12 32 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_32 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 32) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_32 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_32 : oddCount 32 12 = 4 ∧ acceleratedOrbit 12 32 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_32 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 32) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_32.1, data_12_32.2]

/-- Complete interval computation for depth 12, residue 33. -/
theorem bounds_12_33 : exactInterval 12 33 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_33 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 33) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_33 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_33 : oddCount 33 12 = 7 ∧ acceleratedOrbit 12 33 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_33 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 33) = 3 ^ 7 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_33.1, data_12_33.2]

/-- Complete interval computation for depth 12, residue 34. -/
theorem bounds_12_34 : exactInterval 12 34 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_34 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 34) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_34 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_34 : oddCount 34 12 = 4 ∧ acceleratedOrbit 12 34 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_34 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 34) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_34.1, data_12_34.2]

/-- Complete interval computation for depth 12, residue 35. -/
theorem bounds_12_35 : exactInterval 12 35 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_35 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 35) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_35 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_35 : oddCount 35 12 = 4 ∧ acceleratedOrbit 12 35 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_35 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 35) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_35.1, data_12_35.2]

/-- Complete interval computation for depth 12, residue 36. -/
theorem bounds_12_36 : exactInterval 12 36 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_36 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 36) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_36 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_36 : oddCount 36 12 = 6 ∧ acceleratedOrbit 12 36 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_36 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 36) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_36.1, data_12_36.2]

/-- Complete interval computation for depth 12, residue 37. -/
theorem bounds_12_37 : exactInterval 12 37 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_37 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 37) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_37 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_37 : oddCount 37 12 = 6 ∧ acceleratedOrbit 12 37 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_37 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 37) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_37.1, data_12_37.2]

/-- Complete interval computation for depth 12, residue 38. -/
theorem bounds_12_38 : exactInterval 12 38 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_38 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 38) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_38 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_38 : oddCount 38 12 = 6 ∧ acceleratedOrbit 12 38 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_38 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 38) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_38.1, data_12_38.2]

/-- Complete interval computation for depth 12, residue 39. -/
theorem bounds_12_39 : exactInterval 12 39 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_39 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 39) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_39 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_39 : oddCount 39 12 = 7 ∧ acceleratedOrbit 12 39 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_39 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 39) = 3 ^ 7 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_39.1, data_12_39.2]

/-- Complete interval computation for depth 12, residue 40. -/
theorem bounds_12_40 : exactInterval 12 40 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_40 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 40) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_40 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_40 : oddCount 40 12 = 4 ∧ acceleratedOrbit 12 40 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_40 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 40) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_40.1, data_12_40.2]

/-- Complete interval computation for depth 12, residue 41. -/
theorem bounds_12_41 : exactInterval 12 41 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_41 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 41) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_41 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_41 : oddCount 41 12 = 9 ∧ acceleratedOrbit 12 41 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_41 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 41) = 3 ^ 9 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_41.1, data_12_41.2]

/-- Complete interval computation for depth 12, residue 42. -/
theorem bounds_12_42 : exactInterval 12 42 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_42 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 42) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_42 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_42 : oddCount 42 12 = 4 ∧ acceleratedOrbit 12 42 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_42 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 42) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_42.1, data_12_42.2]

/-- Complete interval computation for depth 12, residue 43. -/
theorem bounds_12_43 : exactInterval 12 43 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_43 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 43) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_43 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_43 : oddCount 43 12 = 7 ∧ acceleratedOrbit 12 43 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_43 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 43) = 3 ^ 7 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_43.1, data_12_43.2]

/-- Complete interval computation for depth 12, residue 44. -/
theorem bounds_12_44 : exactInterval 12 44 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_44 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 44) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_44 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_44 : oddCount 44 12 = 4 ∧ acceleratedOrbit 12 44 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_44 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 44) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_44.1, data_12_44.2]

/-- Complete interval computation for depth 12, residue 45. -/
theorem bounds_12_45 : exactInterval 12 45 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_45 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 45) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_45 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_45 : oddCount 45 12 = 4 ∧ acceleratedOrbit 12 45 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_45 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 45) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_45.1, data_12_45.2]

end Collatz.Research.StoppingAtlas.Batch0203
