import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0471

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 51. -/
theorem bounds_13_51 : exactInterval 13 51 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_51 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 51) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_51 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_51 : oddCount 51 13 = 6 ∧ acceleratedOrbit 13 51 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_51 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 51) = 3 ^ 6 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_51.1, data_13_51.2]

/-- Complete interval computation for depth 13, residue 52. -/
theorem bounds_13_52 : exactInterval 13 52 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_52 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 52) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_52 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_52 : oddCount 52 13 = 4 ∧ acceleratedOrbit 13 52 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_52 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 52) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_52.1, data_13_52.2]

/-- Complete interval computation for depth 13, residue 53. -/
theorem bounds_13_53 : exactInterval 13 53 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_53 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 53) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_53 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_53 : oddCount 53 13 = 4 ∧ acceleratedOrbit 13 53 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_53 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 53) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_53.1, data_13_53.2]

/-- Complete interval computation for depth 13, residue 54. -/
theorem bounds_13_54 : exactInterval 13 54 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_54 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 54) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_54 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_54 : oddCount 54 13 = 9 ∧ acceleratedOrbit 13 54 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_54 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 54) = 3 ^ 9 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_54.1, data_13_54.2]

/-- Complete interval computation for depth 13, residue 55. -/
theorem bounds_13_55 : exactInterval 13 55 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_55 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 55) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_55 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_55 : oddCount 55 13 = 9 ∧ acceleratedOrbit 13 55 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_55 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 55) = 3 ^ 9 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_55.1, data_13_55.2]

/-- Complete interval computation for depth 13, residue 56. -/
theorem bounds_13_56 : exactInterval 13 56 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_56 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 56) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_56 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_56 : oddCount 56 13 = 5 ∧ acceleratedOrbit 13 56 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_56 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 56) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_56.1, data_13_56.2]

/-- Complete interval computation for depth 13, residue 57. -/
theorem bounds_13_57 : exactInterval 13 57 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_57 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 57) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_57 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_57 : oddCount 57 13 = 7 ∧ acceleratedOrbit 13 57 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_57 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 57) = 3 ^ 7 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_57.1, data_13_57.2]

/-- Complete interval computation for depth 13, residue 58. -/
theorem bounds_13_58 : exactInterval 13 58 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_58 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 58) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_58 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_58 : oddCount 58 13 = 5 ∧ acceleratedOrbit 13 58 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_58 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 58) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_58.1, data_13_58.2]

/-- Complete interval computation for depth 13, residue 59. -/
theorem bounds_13_59 : exactInterval 13 59 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_59 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 59) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_59 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_59 : oddCount 59 13 = 7 ∧ acceleratedOrbit 13 59 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_59 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 59) = 3 ^ 7 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_59.1, data_13_59.2]

/-- Complete interval computation for depth 13, residue 60. -/
theorem bounds_13_60 : exactInterval 13 60 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_60 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 60) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_60 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_60 : oddCount 60 13 = 5 ∧ acceleratedOrbit 13 60 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_60 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 60) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_60.1, data_13_60.2]

/-- Complete interval computation for depth 13, residue 61. -/
theorem bounds_13_61 : exactInterval 13 61 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_61 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 61) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_61 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_61 : oddCount 61 13 = 5 ∧ acceleratedOrbit 13 61 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_61 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 61) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_61.1, data_13_61.2]

/-- Complete interval computation for depth 13, residue 62. -/
theorem bounds_13_62 : exactInterval 13 62 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_62 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 62) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_62 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_62 : oddCount 62 13 = 9 ∧ acceleratedOrbit 13 62 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_62 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 62) = 3 ^ 9 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_62.1, data_13_62.2]

/-- Complete interval computation for depth 13, residue 63. -/
theorem bounds_13_63 : exactInterval 13 63 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_63 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 63) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_63 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_63 : oddCount 63 13 = 9 ∧ acceleratedOrbit 13 63 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_63 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 63) = 3 ^ 9 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_63.1, data_13_63.2]

/-- Complete interval computation for depth 13, residue 64. -/
theorem bounds_13_64 : exactInterval 13 64 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_64 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 64) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_64 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_64 : oddCount 64 13 = 4 ∧ acceleratedOrbit 13 64 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_64 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 64) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_64.1, data_13_64.2]

/-- Complete interval computation for depth 13, residue 65. -/
theorem bounds_13_65 : exactInterval 13 65 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_65 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 65) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_65 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_65 : oddCount 65 13 = 7 ∧ acceleratedOrbit 13 65 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_65 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 65) = 3 ^ 7 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_65.1, data_13_65.2]

end Collatz.Research.StoppingAtlas.Batch0471
