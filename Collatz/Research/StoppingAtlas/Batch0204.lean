import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0204

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 46. -/
theorem bounds_12_46 : exactInterval 12 46 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_46 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 46) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_46 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_46 : oddCount 46 12 = 4 ∧ acceleratedOrbit 12 46 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_46 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 46) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_46.1, data_12_46.2]

/-- Complete interval computation for depth 12, residue 47. -/
theorem bounds_12_47 : exactInterval 12 47 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_47 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 47) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_47 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_47 : oddCount 47 12 = 9 ∧ acceleratedOrbit 12 47 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_47 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 47) = 3 ^ 9 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_47.1, data_12_47.2]

/-- Complete interval computation for depth 12, residue 48. -/
theorem bounds_12_48 : exactInterval 12 48 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_48 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 48) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_48 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_48 : oddCount 48 12 = 4 ∧ acceleratedOrbit 12 48 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_48 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 48) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_48.1, data_12_48.2]

/-- Complete interval computation for depth 12, residue 49. -/
theorem bounds_12_49 : exactInterval 12 49 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_49 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 49) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_49 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_49 : oddCount 49 12 = 6 ∧ acceleratedOrbit 12 49 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_49 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 49) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_49.1, data_12_49.2]

/-- Complete interval computation for depth 12, residue 50. -/
theorem bounds_12_50 : exactInterval 12 50 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_50 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 50) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_50 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_50 : oddCount 50 12 = 6 ∧ acceleratedOrbit 12 50 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_50 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 50) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_50.1, data_12_50.2]

/-- Complete interval computation for depth 12, residue 51. -/
theorem bounds_12_51 : exactInterval 12 51 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_51 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 51) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_51 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_51 : oddCount 51 12 = 6 ∧ acceleratedOrbit 12 51 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_51 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 51) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_51.1, data_12_51.2]

/-- Complete interval computation for depth 12, residue 52. -/
theorem bounds_12_52 : exactInterval 12 52 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_52 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 52) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_52 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_52 : oddCount 52 12 = 4 ∧ acceleratedOrbit 12 52 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_52 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 52) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_52.1, data_12_52.2]

/-- Complete interval computation for depth 12, residue 53. -/
theorem bounds_12_53 : exactInterval 12 53 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_53 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 53) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_53 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_53 : oddCount 53 12 = 4 ∧ acceleratedOrbit 12 53 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_53 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 53) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_53.1, data_12_53.2]

/-- Complete interval computation for depth 12, residue 54. -/
theorem bounds_12_54 : exactInterval 12 54 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_54 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 54) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_54 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_54 : oddCount 54 12 = 8 ∧ acceleratedOrbit 12 54 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_54 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 54) = 3 ^ 8 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_54.1, data_12_54.2]

/-- Complete interval computation for depth 12, residue 55. -/
theorem bounds_12_55 : exactInterval 12 55 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_55 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 55) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_55 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_55 : oddCount 55 12 = 8 ∧ acceleratedOrbit 12 55 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_55 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 55) = 3 ^ 8 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_55.1, data_12_55.2]

/-- Complete interval computation for depth 12, residue 56. -/
theorem bounds_12_56 : exactInterval 12 56 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_56 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 56) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_56 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_56 : oddCount 56 12 = 5 ∧ acceleratedOrbit 12 56 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_56 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 56) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_56.1, data_12_56.2]

/-- Complete interval computation for depth 12, residue 57. -/
theorem bounds_12_57 : exactInterval 12 57 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_57 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 57) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_57 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_57 : oddCount 57 12 = 6 ∧ acceleratedOrbit 12 57 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_57 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 57) = 3 ^ 6 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_57.1, data_12_57.2]

/-- Complete interval computation for depth 12, residue 58. -/
theorem bounds_12_58 : exactInterval 12 58 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_58 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 58) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_58 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_58 : oddCount 58 12 = 5 ∧ acceleratedOrbit 12 58 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_58 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 58) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_58.1, data_12_58.2]

/-- Complete interval computation for depth 12, residue 59. -/
theorem bounds_12_59 : exactInterval 12 59 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_59 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 59) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_59 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_59 : oddCount 59 12 = 6 ∧ acceleratedOrbit 12 59 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_59 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 59) = 3 ^ 6 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_59.1, data_12_59.2]

/-- Complete interval computation for depth 12, residue 60. -/
theorem bounds_12_60 : exactInterval 12 60 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_60 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 60) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_60 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_60 : oddCount 60 12 = 5 ∧ acceleratedOrbit 12 60 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_60 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 60) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_60.1, data_12_60.2]

end Collatz.Research.StoppingAtlas.Batch0204
