import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0071

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 51. -/
theorem bounds_11_51 : exactInterval 11 51 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_51 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 51) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_51 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_51 : oddCount 51 11 = 6 ∧ acceleratedOrbit 11 51 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_51 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 51) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_51.1, data_11_51.2]

/-- Complete interval computation for depth 11, residue 52. -/
theorem bounds_11_52 : exactInterval 11 52 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_52 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 52) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_52 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_52 : oddCount 52 11 = 3 ∧ acceleratedOrbit 11 52 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_52 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 52) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_52.1, data_11_52.2]

/-- Complete interval computation for depth 11, residue 53. -/
theorem bounds_11_53 : exactInterval 11 53 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_53 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 53) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_53 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_53 : oddCount 53 11 = 3 ∧ acceleratedOrbit 11 53 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_53 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 53) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_53.1, data_11_53.2]

/-- Complete interval computation for depth 11, residue 54. -/
theorem bounds_11_54 : exactInterval 11 54 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_54 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 54) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_54 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_54 : oddCount 54 11 = 8 ∧ acceleratedOrbit 11 54 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_54 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 54) = 3 ^ 8 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_54.1, data_11_54.2]

/-- Complete interval computation for depth 11, residue 55. -/
theorem bounds_11_55 : exactInterval 11 55 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_55 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 55) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_55 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_55 : oddCount 55 11 = 8 ∧ acceleratedOrbit 11 55 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_55 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 55) = 3 ^ 8 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_55.1, data_11_55.2]

/-- Complete interval computation for depth 11, residue 56. -/
theorem bounds_11_56 : exactInterval 11 56 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_56 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 56) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_56 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_56 : oddCount 56 11 = 5 ∧ acceleratedOrbit 11 56 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_56 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 56) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_56.1, data_11_56.2]

/-- Complete interval computation for depth 11, residue 57. -/
theorem bounds_11_57 : exactInterval 11 57 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_57 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 57) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_57 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_57 : oddCount 57 11 = 5 ∧ acceleratedOrbit 11 57 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_57 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 57) = 3 ^ 5 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_57.1, data_11_57.2]

/-- Complete interval computation for depth 11, residue 58. -/
theorem bounds_11_58 : exactInterval 11 58 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_58 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 58) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_58 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_58 : oddCount 58 11 = 5 ∧ acceleratedOrbit 11 58 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_58 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 58) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_58.1, data_11_58.2]

/-- Complete interval computation for depth 11, residue 59. -/
theorem bounds_11_59 : exactInterval 11 59 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_59 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 59) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_59 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_59 : oddCount 59 11 = 6 ∧ acceleratedOrbit 11 59 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_59 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 59) = 3 ^ 6 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_59.1, data_11_59.2]

/-- Complete interval computation for depth 11, residue 60. -/
theorem bounds_11_60 : exactInterval 11 60 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_60 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 60) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_60 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_60 : oddCount 60 11 = 5 ∧ acceleratedOrbit 11 60 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_60 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 60) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_60.1, data_11_60.2]

/-- Complete interval computation for depth 11, residue 61. -/
theorem bounds_11_61 : exactInterval 11 61 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_61 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 61) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_61 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_61 : oddCount 61 11 = 5 ∧ acceleratedOrbit 11 61 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_61 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 61) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_61.1, data_11_61.2]

/-- Complete interval computation for depth 11, residue 62. -/
theorem bounds_11_62 : exactInterval 11 62 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_62 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 62) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_62 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_62 : oddCount 62 11 = 8 ∧ acceleratedOrbit 11 62 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_62 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 62) = 3 ^ 8 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_62.1, data_11_62.2]

/-- Complete interval computation for depth 11, residue 63. -/
theorem bounds_11_63 : exactInterval 11 63 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_63 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 63) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_63 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_63 : oddCount 63 11 = 8 ∧ acceleratedOrbit 11 63 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_63 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 63) = 3 ^ 8 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_63.1, data_11_63.2]

/-- Complete interval computation for depth 11, residue 64. -/
theorem bounds_11_64 : exactInterval 11 64 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_64 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 64) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_64 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_64 : oddCount 64 11 = 3 ∧ acceleratedOrbit 11 64 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_64 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 64) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_64.1, data_11_64.2]

/-- Complete interval computation for depth 11, residue 65. -/
theorem bounds_11_65 : exactInterval 11 65 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_65 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 65) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_65 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_65 : oddCount 65 11 = 6 ∧ acceleratedOrbit 11 65 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_65 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 65) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_65.1, data_11_65.2]

end Collatz.Research.StoppingAtlas.Batch0071
