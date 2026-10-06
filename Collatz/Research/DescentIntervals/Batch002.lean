import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch002

/-- Complete interval computation for depth 3, residue 4. -/
theorem bounds_3_4 : exactInterval 3 4 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_3_4 (m : Nat) :
    stoppingTime (2 ^ 3 * m + 4) 3 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_3_4 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_3_4 : oddCount 4 3 = 1 ∧ acceleratedOrbit 3 4 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_3_4 (m : Nat) :
    acceleratedOrbit 3 (2 ^ 3 * m + 4) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_3_4.1, data_3_4.2]

/-- Complete interval computation for depth 3, residue 5. -/
theorem bounds_3_5 : exactInterval 3 5 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_3_5 (m : Nat) :
    stoppingTime (2 ^ 3 * m + 5) 3 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_3_5 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_3_5 : oddCount 5 3 = 1 ∧ acceleratedOrbit 3 5 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_3_5 (m : Nat) :
    acceleratedOrbit 3 (2 ^ 3 * m + 5) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_3_5.1, data_3_5.2]

/-- Complete interval computation for depth 3, residue 6. -/
theorem bounds_3_6 : exactInterval 3 6 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_3_6 (m : Nat) :
    stoppingTime (2 ^ 3 * m + 6) 3 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_3_6 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_3_6 : oddCount 6 3 = 2 ∧ acceleratedOrbit 3 6 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_3_6 (m : Nat) :
    acceleratedOrbit 3 (2 ^ 3 * m + 6) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_3_6.1, data_3_6.2]

/-- Complete interval computation for depth 3, residue 7. -/
theorem bounds_3_7 : exactInterval 3 7 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_3_7 (m : Nat) :
    stoppingTime (2 ^ 3 * m + 7) 3 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_3_7 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_3_7 : oddCount 7 3 = 3 ∧ acceleratedOrbit 3 7 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_3_7 (m : Nat) :
    acceleratedOrbit 3 (2 ^ 3 * m + 7) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_3_7.1, data_3_7.2]

/-- Complete interval computation for depth 4, residue 0. -/
theorem bounds_4_0 : exactInterval 4 0 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_4_0 (m : Nat) :
    stoppingTime (2 ^ 4 * m + 0) 4 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_4_0 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_4_0 : oddCount 0 4 = 0 ∧ acceleratedOrbit 4 0 = 0 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_4_0 (m : Nat) :
    acceleratedOrbit 4 (2 ^ 4 * m + 0) = 3 ^ 0 * m + 0 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_4_0.1, data_4_0.2]

/-- Complete interval computation for depth 4, residue 1. -/
theorem bounds_4_1 : exactInterval 4 1 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_4_1 (m : Nat) :
    stoppingTime (2 ^ 4 * m + 1) 4 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_4_1 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_4_1 : oddCount 1 4 = 2 ∧ acceleratedOrbit 4 1 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_4_1 (m : Nat) :
    acceleratedOrbit 4 (2 ^ 4 * m + 1) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_4_1.1, data_4_1.2]

/-- Complete interval computation for depth 4, residue 2. -/
theorem bounds_4_2 : exactInterval 4 2 = ⟨1, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_4_2 (m : Nat) :
    stoppingTime (2 ^ 4 * m + 2) 4 ↔ 1 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_4_2 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_4_2 : oddCount 2 4 = 2 ∧ acceleratedOrbit 4 2 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_4_2 (m : Nat) :
    acceleratedOrbit 4 (2 ^ 4 * m + 2) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_4_2.1, data_4_2.2]

/-- Complete interval computation for depth 4, residue 3. -/
theorem bounds_4_3 : exactInterval 4 3 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_4_3 (m : Nat) :
    stoppingTime (2 ^ 4 * m + 3) 4 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_4_3 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_4_3 : oddCount 3 4 = 2 ∧ acceleratedOrbit 4 3 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_4_3 (m : Nat) :
    acceleratedOrbit 4 (2 ^ 4 * m + 3) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_4_3.1, data_4_3.2]

/-- Complete interval computation for depth 4, residue 4. -/
theorem bounds_4_4 : exactInterval 4 4 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_4_4 (m : Nat) :
    stoppingTime (2 ^ 4 * m + 4) 4 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_4_4 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_4_4 : oddCount 4 4 = 1 ∧ acceleratedOrbit 4 4 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_4_4 (m : Nat) :
    acceleratedOrbit 4 (2 ^ 4 * m + 4) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_4_4.1, data_4_4.2]

/-- Complete interval computation for depth 4, residue 5. -/
theorem bounds_4_5 : exactInterval 4 5 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_4_5 (m : Nat) :
    stoppingTime (2 ^ 4 * m + 5) 4 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_4_5 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_4_5 : oddCount 5 4 = 1 ∧ acceleratedOrbit 4 5 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_4_5 (m : Nat) :
    acceleratedOrbit 4 (2 ^ 4 * m + 5) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_4_5.1, data_4_5.2]

end Collatz.Research.DescentIntervals.Batch002
