import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch004

/-- Complete interval computation for depth 5, residue 0. -/
theorem bounds_5_0 : exactInterval 5 0 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_0 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 0) 5 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_0 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_0 : oddCount 0 5 = 0 ∧ acceleratedOrbit 5 0 = 0 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_0 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 0) = 3 ^ 0 * m + 0 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_0.1, data_5_0.2]

/-- Complete interval computation for depth 5, residue 1. -/
theorem bounds_5_1 : exactInterval 5 1 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_1 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 1) 5 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_1 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_1 : oddCount 1 5 = 3 ∧ acceleratedOrbit 5 1 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_1 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 1) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_1.1, data_5_1.2]

/-- Complete interval computation for depth 5, residue 2. -/
theorem bounds_5_2 : exactInterval 5 2 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_2 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 2) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_2 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_2 : oddCount 2 5 = 2 ∧ acceleratedOrbit 5 2 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_2 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 2) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_2.1, data_5_2.2]

/-- Complete interval computation for depth 5, residue 3. -/
theorem bounds_5_3 : exactInterval 5 3 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_3 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 3) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_3 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_3 : oddCount 3 5 = 2 ∧ acceleratedOrbit 5 3 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_3 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 3) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_3.1, data_5_3.2]

/-- Complete interval computation for depth 5, residue 4. -/
theorem bounds_5_4 : exactInterval 5 4 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_4 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 4) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_4 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_4 : oddCount 4 5 = 2 ∧ acceleratedOrbit 5 4 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_4 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 4) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_4.1, data_5_4.2]

/-- Complete interval computation for depth 5, residue 5. -/
theorem bounds_5_5 : exactInterval 5 5 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_5 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 5) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_5 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_5 : oddCount 5 5 = 2 ∧ acceleratedOrbit 5 5 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_5 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 5) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_5.1, data_5_5.2]

/-- Complete interval computation for depth 5, residue 6. -/
theorem bounds_5_6 : exactInterval 5 6 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_6 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 6) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_6 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_6 : oddCount 6 5 = 2 ∧ acceleratedOrbit 5 6 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_6 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 6) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_6.1, data_5_6.2]

/-- Complete interval computation for depth 5, residue 7. -/
theorem bounds_5_7 : exactInterval 5 7 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_7 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 7) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_7 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_7 : oddCount 7 5 = 4 ∧ acceleratedOrbit 5 7 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_7 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 7) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_7.1, data_5_7.2]

/-- Complete interval computation for depth 5, residue 8. -/
theorem bounds_5_8 : exactInterval 5 8 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_8 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 8) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_8 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_8 : oddCount 8 5 = 1 ∧ acceleratedOrbit 5 8 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_8 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 8) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_8.1, data_5_8.2]

/-- Complete interval computation for depth 5, residue 9. -/
theorem bounds_5_9 : exactInterval 5 9 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_9 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 9) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_9 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_9 : oddCount 9 5 = 4 ∧ acceleratedOrbit 5 9 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_9 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 9) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_9.1, data_5_9.2]

end Collatz.Research.DescentIntervals.Batch004
