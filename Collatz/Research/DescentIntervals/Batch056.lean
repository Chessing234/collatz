import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch056

/-- Complete interval computation for depth 9, residue 52. -/
theorem bounds_9_52 : exactInterval 9 52 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_52 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 52) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_52 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_52 : oddCount 52 9 = 2 ∧ acceleratedOrbit 9 52 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_52 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 52) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_52.1, data_9_52.2]

/-- Complete interval computation for depth 9, residue 53. -/
theorem bounds_9_53 : exactInterval 9 53 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_53 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 53) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_53 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_53 : oddCount 53 9 = 2 ∧ acceleratedOrbit 9 53 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_53 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 53) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_53.1, data_9_53.2]

/-- Complete interval computation for depth 9, residue 54. -/
theorem bounds_9_54 : exactInterval 9 54 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_54 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 54) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_54 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_54 : oddCount 54 9 = 7 ∧ acceleratedOrbit 9 54 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_54 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 54) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_54.1, data_9_54.2]

/-- Complete interval computation for depth 9, residue 55. -/
theorem bounds_9_55 : exactInterval 9 55 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_55 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 55) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_55 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_55 : oddCount 55 9 = 7 ∧ acceleratedOrbit 9 55 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_55 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 55) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_55.1, data_9_55.2]

/-- Complete interval computation for depth 9, residue 56. -/
theorem bounds_9_56 : exactInterval 9 56 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_56 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 56) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_56 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_56 : oddCount 56 9 = 4 ∧ acceleratedOrbit 9 56 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_56 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 56) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_56.1, data_9_56.2]

/-- Complete interval computation for depth 9, residue 57. -/
theorem bounds_9_57 : exactInterval 9 57 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_57 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 57) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_57 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_57 : oddCount 57 9 = 5 ∧ acceleratedOrbit 9 57 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_57 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 57) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_57.1, data_9_57.2]

/-- Complete interval computation for depth 9, residue 58. -/
theorem bounds_9_58 : exactInterval 9 58 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_58 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 58) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_58 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_58 : oddCount 58 9 = 4 ∧ acceleratedOrbit 9 58 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_58 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 58) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_58.1, data_9_58.2]

/-- Complete interval computation for depth 9, residue 59. -/
theorem bounds_9_59 : exactInterval 9 59 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_59 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 59) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_59 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_59 : oddCount 59 9 = 5 ∧ acceleratedOrbit 9 59 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_59 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 59) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_59.1, data_9_59.2]

/-- Complete interval computation for depth 9, residue 60. -/
theorem bounds_9_60 : exactInterval 9 60 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_60 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 60) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_60 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_60 : oddCount 60 9 = 4 ∧ acceleratedOrbit 9 60 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_60 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 60) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_60.1, data_9_60.2]

/-- Complete interval computation for depth 9, residue 61. -/
theorem bounds_9_61 : exactInterval 9 61 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_61 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 61) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_61 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_61 : oddCount 61 9 = 4 ∧ acceleratedOrbit 9 61 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_61 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 61) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_61.1, data_9_61.2]

end Collatz.Research.DescentIntervals.Batch056
