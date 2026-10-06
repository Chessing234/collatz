import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch031

/-- Complete interval computation for depth 8, residue 52. -/
theorem bounds_8_52 : exactInterval 8 52 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_52 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 52) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_52 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_52 : oddCount 52 8 = 2 ∧ acceleratedOrbit 8 52 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_52 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 52) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_52.1, data_8_52.2]

/-- Complete interval computation for depth 8, residue 53. -/
theorem bounds_8_53 : exactInterval 8 53 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_53 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 53) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_53 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_53 : oddCount 53 8 = 2 ∧ acceleratedOrbit 8 53 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_53 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 53) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_53.1, data_8_53.2]

/-- Complete interval computation for depth 8, residue 54. -/
theorem bounds_8_54 : exactInterval 8 54 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_54 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 54) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_54 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_54 : oddCount 54 8 = 6 ∧ acceleratedOrbit 8 54 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_54 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 54) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_54.1, data_8_54.2]

/-- Complete interval computation for depth 8, residue 55. -/
theorem bounds_8_55 : exactInterval 8 55 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_55 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 55) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_55 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_55 : oddCount 55 8 = 6 ∧ acceleratedOrbit 8 55 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_55 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 55) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_55.1, data_8_55.2]

/-- Complete interval computation for depth 8, residue 56. -/
theorem bounds_8_56 : exactInterval 8 56 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_56 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 56) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_56 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_56 : oddCount 56 8 = 4 ∧ acceleratedOrbit 8 56 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_56 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 56) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_56.1, data_8_56.2]

/-- Complete interval computation for depth 8, residue 57. -/
theorem bounds_8_57 : exactInterval 8 57 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_57 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 57) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_57 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_57 : oddCount 57 8 = 5 ∧ acceleratedOrbit 8 57 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_57 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 57) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_57.1, data_8_57.2]

/-- Complete interval computation for depth 8, residue 58. -/
theorem bounds_8_58 : exactInterval 8 58 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_58 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 58) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_58 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_58 : oddCount 58 8 = 4 ∧ acceleratedOrbit 8 58 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_58 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 58) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_58.1, data_8_58.2]

/-- Complete interval computation for depth 8, residue 59. -/
theorem bounds_8_59 : exactInterval 8 59 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_59 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 59) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_59 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_59 : oddCount 59 8 = 4 ∧ acceleratedOrbit 8 59 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_59 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 59) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_59.1, data_8_59.2]

/-- Complete interval computation for depth 8, residue 60. -/
theorem bounds_8_60 : exactInterval 8 60 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_60 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 60) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_60 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_60 : oddCount 60 8 = 4 ∧ acceleratedOrbit 8 60 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_60 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 60) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_60.1, data_8_60.2]

/-- Complete interval computation for depth 8, residue 61. -/
theorem bounds_8_61 : exactInterval 8 61 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_61 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 61) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_61 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_61 : oddCount 61 8 = 4 ∧ acceleratedOrbit 8 61 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_61 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 61) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_61.1, data_8_61.2]

end Collatz.Research.DescentIntervals.Batch031
