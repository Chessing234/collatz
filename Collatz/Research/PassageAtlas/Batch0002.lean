import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0002

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32. -/
theorem bounds_15_32 : exactInterval 15 32 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32 : oddCount 32 15 = 5 ∧ acceleratedOrbit 15 32 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32.1, data_15_32.2]

/-- Complete interval computation for depth 15, residue 33. -/
theorem bounds_15_33 : exactInterval 15 33 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_33 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 33) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_33 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_33 : oddCount 33 15 = 8 ∧ acceleratedOrbit 15 33 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_33 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 33) = 3 ^ 8 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_33.1, data_15_33.2]

/-- Complete interval computation for depth 15, residue 34. -/
theorem bounds_15_34 : exactInterval 15 34 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_34 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 34) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_34 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_34 : oddCount 34 15 = 6 ∧ acceleratedOrbit 15 34 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_34 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 34) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_34.1, data_15_34.2]

/-- Complete interval computation for depth 15, residue 35. -/
theorem bounds_15_35 : exactInterval 15 35 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_35 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 35) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_35 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_35 : oddCount 35 15 = 6 ∧ acceleratedOrbit 15 35 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_35 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 35) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_35.1, data_15_35.2]

/-- Complete interval computation for depth 15, residue 36. -/
theorem bounds_15_36 : exactInterval 15 36 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_36 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 36) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_36 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_36 : oddCount 36 15 = 6 ∧ acceleratedOrbit 15 36 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_36 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 36) = 3 ^ 6 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_36.1, data_15_36.2]

/-- Complete interval computation for depth 15, residue 37. -/
theorem bounds_15_37 : exactInterval 15 37 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_37 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 37) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_37 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_37 : oddCount 37 15 = 6 ∧ acceleratedOrbit 15 37 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_37 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 37) = 3 ^ 6 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_37.1, data_15_37.2]

/-- Complete interval computation for depth 15, residue 38. -/
theorem bounds_15_38 : exactInterval 15 38 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_38 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 38) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_38 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_38 : oddCount 38 15 = 6 ∧ acceleratedOrbit 15 38 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_38 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 38) = 3 ^ 6 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_38.1, data_15_38.2]

/-- Complete interval computation for depth 15, residue 39. -/
theorem bounds_15_39 : exactInterval 15 39 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_39 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 39) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_39 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_39 : oddCount 39 15 = 9 ∧ acceleratedOrbit 15 39 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_39 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 39) = 3 ^ 9 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_39.1, data_15_39.2]

/-- Complete interval computation for depth 15, residue 40. -/
theorem bounds_15_40 : exactInterval 15 40 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_40 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 40) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_40 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_40 : oddCount 40 15 = 5 ∧ acceleratedOrbit 15 40 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_40 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 40) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_40.1, data_15_40.2]

/-- Complete interval computation for depth 15, residue 41. -/
theorem bounds_15_41 : exactInterval 15 41 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_41 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 41) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_41 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_41 : oddCount 41 15 = 11 ∧ acceleratedOrbit 15 41 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_41 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 41) = 3 ^ 11 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_41.1, data_15_41.2]

/-- Complete interval computation for depth 15, residue 42. -/
theorem bounds_15_42 : exactInterval 15 42 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_42 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 42) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_42 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_42 : oddCount 42 15 = 5 ∧ acceleratedOrbit 15 42 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_42 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 42) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_42.1, data_15_42.2]

/-- Complete interval computation for depth 15, residue 43. -/
theorem bounds_15_43 : exactInterval 15 43 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_43 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 43) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_43 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_43 : oddCount 43 15 = 8 ∧ acceleratedOrbit 15 43 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_43 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 43) = 3 ^ 8 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_43.1, data_15_43.2]

/-- Complete interval computation for depth 15, residue 44. -/
theorem bounds_15_44 : exactInterval 15 44 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_44 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 44) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_44 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_44 : oddCount 44 15 = 6 ∧ acceleratedOrbit 15 44 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_44 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 44) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_44.1, data_15_44.2]

/-- Complete interval computation for depth 15, residue 45. -/
theorem bounds_15_45 : exactInterval 15 45 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_45 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 45) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_45 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_45 : oddCount 45 15 = 6 ∧ acceleratedOrbit 15 45 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_45 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 45) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_45.1, data_15_45.2]

/-- Complete interval computation for depth 15, residue 46. -/
theorem bounds_15_46 : exactInterval 15 46 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_46 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 46) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_46 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_46 : oddCount 46 15 = 6 ∧ acceleratedOrbit 15 46 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_46 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 46) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_46.1, data_15_46.2]

/-- Complete interval computation for depth 15, residue 47. -/
theorem bounds_15_47 : exactInterval 15 47 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_47 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 47) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_47 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_47 : oddCount 47 15 = 11 ∧ acceleratedOrbit 15 47 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_47 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 47) = 3 ^ 11 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_47.1, data_15_47.2]

/-- Complete interval computation for depth 15, residue 48. -/
theorem bounds_15_48 : exactInterval 15 48 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_48 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 48) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_48 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_48 : oddCount 48 15 = 5 ∧ acceleratedOrbit 15 48 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_48 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 48) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_48.1, data_15_48.2]

/-- Complete interval computation for depth 15, residue 49. -/
theorem bounds_15_49 : exactInterval 15 49 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_49 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 49) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_49 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_49 : oddCount 49 15 = 7 ∧ acceleratedOrbit 15 49 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_49 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 49) = 3 ^ 7 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_49.1, data_15_49.2]

/-- Complete interval computation for depth 15, residue 50. -/
theorem bounds_15_50 : exactInterval 15 50 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_50 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 50) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_50 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_50 : oddCount 50 15 = 7 ∧ acceleratedOrbit 15 50 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_50 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 50) = 3 ^ 7 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_50.1, data_15_50.2]

/-- Complete interval computation for depth 15, residue 51. -/
theorem bounds_15_51 : exactInterval 15 51 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_51 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 51) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_51 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_51 : oddCount 51 15 = 7 ∧ acceleratedOrbit 15 51 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_51 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 51) = 3 ^ 7 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_51.1, data_15_51.2]

/-- Complete interval computation for depth 15, residue 52. -/
theorem bounds_15_52 : exactInterval 15 52 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_52 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 52) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_52 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_52 : oddCount 52 15 = 5 ∧ acceleratedOrbit 15 52 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_52 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 52) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_52.1, data_15_52.2]

/-- Complete interval computation for depth 15, residue 53. -/
theorem bounds_15_53 : exactInterval 15 53 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_53 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 53) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_53 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_53 : oddCount 53 15 = 5 ∧ acceleratedOrbit 15 53 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_53 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 53) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_53.1, data_15_53.2]

/-- Complete interval computation for depth 15, residue 54. -/
theorem bounds_15_54 : exactInterval 15 54 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_54 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 54) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_54 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_54 : oddCount 54 15 = 10 ∧ acceleratedOrbit 15 54 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_54 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 54) = 3 ^ 10 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_54.1, data_15_54.2]

/-- Complete interval computation for depth 15, residue 55. -/
theorem bounds_15_55 : exactInterval 15 55 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_55 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 55) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_55 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_55 : oddCount 55 15 = 10 ∧ acceleratedOrbit 15 55 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_55 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 55) = 3 ^ 10 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_55.1, data_15_55.2]

/-- Complete interval computation for depth 15, residue 56. -/
theorem bounds_15_56 : exactInterval 15 56 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_56 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 56) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_56 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_56 : oddCount 56 15 = 6 ∧ acceleratedOrbit 15 56 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_56 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 56) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_56.1, data_15_56.2]

/-- Complete interval computation for depth 15, residue 57. -/
theorem bounds_15_57 : exactInterval 15 57 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_57 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 57) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_57 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_57 : oddCount 57 15 = 8 ∧ acceleratedOrbit 15 57 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_57 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 57) = 3 ^ 8 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_57.1, data_15_57.2]

/-- Complete interval computation for depth 15, residue 58. -/
theorem bounds_15_58 : exactInterval 15 58 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_58 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 58) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_58 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_58 : oddCount 58 15 = 6 ∧ acceleratedOrbit 15 58 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_58 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 58) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_58.1, data_15_58.2]

/-- Complete interval computation for depth 15, residue 59. -/
theorem bounds_15_59 : exactInterval 15 59 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_59 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 59) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_59 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_59 : oddCount 59 15 = 8 ∧ acceleratedOrbit 15 59 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_59 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 59) = 3 ^ 8 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_59.1, data_15_59.2]

/-- Complete interval computation for depth 15, residue 60. -/
theorem bounds_15_60 : exactInterval 15 60 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_60 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 60) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_60 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_60 : oddCount 60 15 = 6 ∧ acceleratedOrbit 15 60 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_60 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 60) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_60.1, data_15_60.2]

/-- Complete interval computation for depth 15, residue 61. -/
theorem bounds_15_61 : exactInterval 15 61 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_61 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 61) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_61 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_61 : oddCount 61 15 = 6 ∧ acceleratedOrbit 15 61 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_61 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 61) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_61.1, data_15_61.2]

/-- Complete interval computation for depth 15, residue 62. -/
theorem bounds_15_62 : exactInterval 15 62 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_62 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 62) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_62 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_62 : oddCount 62 15 = 11 ∧ acceleratedOrbit 15 62 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_62 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 62) = 3 ^ 11 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_62.1, data_15_62.2]

/-- Complete interval computation for depth 15, residue 63. -/
theorem bounds_15_63 : exactInterval 15 63 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_63 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 63) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_63 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_63 : oddCount 63 15 = 11 ∧ acceleratedOrbit 15 63 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_63 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 63) = 3 ^ 11 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_63.1, data_15_63.2]

/-- Complete interval computation for depth 15, residue 64. -/
theorem bounds_15_64 : exactInterval 15 64 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_64 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 64) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_64 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_64 : oddCount 64 15 = 5 ∧ acceleratedOrbit 15 64 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_64 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 64) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_64.1, data_15_64.2]

end Collatz.Research.PassageAtlas.Batch0002
