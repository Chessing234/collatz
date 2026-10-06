import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0004

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 46. -/
theorem bounds_10_46 : exactInterval 10 46 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_46 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 46) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_46 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_46 : oddCount 46 10 = 4 ∧ acceleratedOrbit 10 46 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_46 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 46) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_46.1, data_10_46.2]

/-- Complete interval computation for depth 10, residue 47. -/
theorem bounds_10_47 : exactInterval 10 47 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_47 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 47) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_47 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_47 : oddCount 47 10 = 7 ∧ acceleratedOrbit 10 47 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_47 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 47) = 3 ^ 7 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_47.1, data_10_47.2]

/-- Complete interval computation for depth 10, residue 48. -/
theorem bounds_10_48 : exactInterval 10 48 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_48 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 48) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_48 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_48 : oddCount 48 10 = 3 ∧ acceleratedOrbit 10 48 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_48 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 48) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_48.1, data_10_48.2]

/-- Complete interval computation for depth 10, residue 49. -/
theorem bounds_10_49 : exactInterval 10 49 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_49 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 49) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_49 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_49 : oddCount 49 10 = 5 ∧ acceleratedOrbit 10 49 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_49 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 49) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_49.1, data_10_49.2]

/-- Complete interval computation for depth 10, residue 50. -/
theorem bounds_10_50 : exactInterval 10 50 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_50 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 50) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_50 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_50 : oddCount 50 10 = 5 ∧ acceleratedOrbit 10 50 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_50 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 50) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_50.1, data_10_50.2]

/-- Complete interval computation for depth 10, residue 51. -/
theorem bounds_10_51 : exactInterval 10 51 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_51 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 51) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_51 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_51 : oddCount 51 10 = 5 ∧ acceleratedOrbit 10 51 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_51 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 51) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_51.1, data_10_51.2]

/-- Complete interval computation for depth 10, residue 52. -/
theorem bounds_10_52 : exactInterval 10 52 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_52 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 52) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_52 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_52 : oddCount 52 10 = 3 ∧ acceleratedOrbit 10 52 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_52 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 52) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_52.1, data_10_52.2]

/-- Complete interval computation for depth 10, residue 53. -/
theorem bounds_10_53 : exactInterval 10 53 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_53 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 53) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_53 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_53 : oddCount 53 10 = 3 ∧ acceleratedOrbit 10 53 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_53 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 53) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_53.1, data_10_53.2]

/-- Complete interval computation for depth 10, residue 54. -/
theorem bounds_10_54 : exactInterval 10 54 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_54 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 54) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_54 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_54 : oddCount 54 10 = 7 ∧ acceleratedOrbit 10 54 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_54 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 54) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_54.1, data_10_54.2]

/-- Complete interval computation for depth 10, residue 55. -/
theorem bounds_10_55 : exactInterval 10 55 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_55 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 55) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_55 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_55 : oddCount 55 10 = 7 ∧ acceleratedOrbit 10 55 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_55 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 55) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_55.1, data_10_55.2]

/-- Complete interval computation for depth 10, residue 56. -/
theorem bounds_10_56 : exactInterval 10 56 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_56 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 56) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_56 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_56 : oddCount 56 10 = 4 ∧ acceleratedOrbit 10 56 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_56 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 56) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_56.1, data_10_56.2]

/-- Complete interval computation for depth 10, residue 57. -/
theorem bounds_10_57 : exactInterval 10 57 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_57 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 57) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_57 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_57 : oddCount 57 10 = 5 ∧ acceleratedOrbit 10 57 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_57 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 57) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_57.1, data_10_57.2]

/-- Complete interval computation for depth 10, residue 58. -/
theorem bounds_10_58 : exactInterval 10 58 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_58 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 58) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_58 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_58 : oddCount 58 10 = 4 ∧ acceleratedOrbit 10 58 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_58 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 58) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_58.1, data_10_58.2]

/-- Complete interval computation for depth 10, residue 59. -/
theorem bounds_10_59 : exactInterval 10 59 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_59 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 59) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_59 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_59 : oddCount 59 10 = 6 ∧ acceleratedOrbit 10 59 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_59 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 59) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_59.1, data_10_59.2]

/-- Complete interval computation for depth 10, residue 60. -/
theorem bounds_10_60 : exactInterval 10 60 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_60 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 60) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_60 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_60 : oddCount 60 10 = 4 ∧ acceleratedOrbit 10 60 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_60 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 60) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_60.1, data_10_60.2]

end Collatz.Research.StoppingAtlas.Batch0004
