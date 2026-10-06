import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch007

/-- Complete interval computation for depth 5, residue 31. -/
theorem bounds_5_31 : exactInterval 5 31 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_31 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 31) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_31 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_31 : oddCount 31 5 = 5 ∧ acceleratedOrbit 5 31 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_31 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 31) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_31.1, data_5_31.2]

/-- Complete interval computation for depth 6, residue 0. -/
theorem bounds_6_0 : exactInterval 6 0 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_0 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 0) 6 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_0 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_0 : oddCount 0 6 = 0 ∧ acceleratedOrbit 6 0 = 0 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_0 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 0) = 3 ^ 0 * m + 0 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_0.1, data_6_0.2]

/-- Complete interval computation for depth 6, residue 1. -/
theorem bounds_6_1 : exactInterval 6 1 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_1 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 1) 6 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_1 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_1 : oddCount 1 6 = 3 ∧ acceleratedOrbit 6 1 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_1 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 1) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_1.1, data_6_1.2]

/-- Complete interval computation for depth 6, residue 2. -/
theorem bounds_6_2 : exactInterval 6 2 = ⟨1, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_2 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 2) 6 ↔ 1 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_2 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_2 : oddCount 2 6 = 3 ∧ acceleratedOrbit 6 2 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_2 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 2) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_2.1, data_6_2.2]

/-- Complete interval computation for depth 6, residue 3. -/
theorem bounds_6_3 : exactInterval 6 3 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_3 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 3) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_3 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_3 : oddCount 3 6 = 3 ∧ acceleratedOrbit 6 3 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_3 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 3) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_3.1, data_6_3.2]

/-- Complete interval computation for depth 6, residue 4. -/
theorem bounds_6_4 : exactInterval 6 4 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_4 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 4) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_4 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_4 : oddCount 4 6 = 2 ∧ acceleratedOrbit 6 4 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_4 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 4) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_4.1, data_6_4.2]

/-- Complete interval computation for depth 6, residue 5. -/
theorem bounds_6_5 : exactInterval 6 5 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_5 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 5) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_5 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_5 : oddCount 5 6 = 2 ∧ acceleratedOrbit 6 5 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_5 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 5) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_5.1, data_6_5.2]

/-- Complete interval computation for depth 6, residue 6. -/
theorem bounds_6_6 : exactInterval 6 6 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_6 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 6) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_6 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_6 : oddCount 6 6 = 2 ∧ acceleratedOrbit 6 6 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_6 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 6) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_6.1, data_6_6.2]

/-- Complete interval computation for depth 6, residue 7. -/
theorem bounds_6_7 : exactInterval 6 7 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_7 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 7) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_7 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_7 : oddCount 7 6 = 4 ∧ acceleratedOrbit 6 7 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_7 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 7) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_7.1, data_6_7.2]

/-- Complete interval computation for depth 6, residue 8. -/
theorem bounds_6_8 : exactInterval 6 8 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_8 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 8) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_8 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_8 : oddCount 8 6 = 2 ∧ acceleratedOrbit 6 8 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_8 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 8) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_8.1, data_6_8.2]

end Collatz.Research.DescentIntervals.Batch007
