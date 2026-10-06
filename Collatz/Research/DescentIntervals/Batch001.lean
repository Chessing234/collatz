import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch001

/-- Complete interval computation for depth 1, residue 0. -/
theorem bounds_1_0 : exactInterval 1 0 = ⟨1, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_1_0 (m : Nat) :
    stoppingTime (2 ^ 1 * m + 0) 1 ↔ 1 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_1_0 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_1_0 : oddCount 0 1 = 0 ∧ acceleratedOrbit 1 0 = 0 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_1_0 (m : Nat) :
    acceleratedOrbit 1 (2 ^ 1 * m + 0) = 3 ^ 0 * m + 0 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_1_0.1, data_1_0.2]

/-- Complete interval computation for depth 1, residue 1. -/
theorem bounds_1_1 : exactInterval 1 1 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_1_1 (m : Nat) :
    stoppingTime (2 ^ 1 * m + 1) 1 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_1_1 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_1_1 : oddCount 1 1 = 1 ∧ acceleratedOrbit 1 1 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_1_1 (m : Nat) :
    acceleratedOrbit 1 (2 ^ 1 * m + 1) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_1_1.1, data_1_1.2]

/-- Complete interval computation for depth 2, residue 0. -/
theorem bounds_2_0 : exactInterval 2 0 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_2_0 (m : Nat) :
    stoppingTime (2 ^ 2 * m + 0) 2 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_2_0 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_2_0 : oddCount 0 2 = 0 ∧ acceleratedOrbit 2 0 = 0 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_2_0 (m : Nat) :
    acceleratedOrbit 2 (2 ^ 2 * m + 0) = 3 ^ 0 * m + 0 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_2_0.1, data_2_0.2]

/-- Complete interval computation for depth 2, residue 1. -/
theorem bounds_2_1 : exactInterval 2 1 = ⟨1, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_2_1 (m : Nat) :
    stoppingTime (2 ^ 2 * m + 1) 2 ↔ 1 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_2_1 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_2_1 : oddCount 1 2 = 1 ∧ acceleratedOrbit 2 1 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_2_1 (m : Nat) :
    acceleratedOrbit 2 (2 ^ 2 * m + 1) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_2_1.1, data_2_1.2]

/-- Complete interval computation for depth 2, residue 2. -/
theorem bounds_2_2 : exactInterval 2 2 = ⟨1, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_2_2 (m : Nat) :
    stoppingTime (2 ^ 2 * m + 2) 2 ↔ 1 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_2_2 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_2_2 : oddCount 2 2 = 1 ∧ acceleratedOrbit 2 2 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_2_2 (m : Nat) :
    acceleratedOrbit 2 (2 ^ 2 * m + 2) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_2_2.1, data_2_2.2]

/-- Complete interval computation for depth 2, residue 3. -/
theorem bounds_2_3 : exactInterval 2 3 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_2_3 (m : Nat) :
    stoppingTime (2 ^ 2 * m + 3) 2 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_2_3 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_2_3 : oddCount 3 2 = 2 ∧ acceleratedOrbit 2 3 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_2_3 (m : Nat) :
    acceleratedOrbit 2 (2 ^ 2 * m + 3) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_2_3.1, data_2_3.2]

/-- Complete interval computation for depth 3, residue 0. -/
theorem bounds_3_0 : exactInterval 3 0 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_3_0 (m : Nat) :
    stoppingTime (2 ^ 3 * m + 0) 3 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_3_0 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_3_0 : oddCount 0 3 = 0 ∧ acceleratedOrbit 3 0 = 0 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_3_0 (m : Nat) :
    acceleratedOrbit 3 (2 ^ 3 * m + 0) = 3 ^ 0 * m + 0 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_3_0.1, data_3_0.2]

/-- Complete interval computation for depth 3, residue 1. -/
theorem bounds_3_1 : exactInterval 3 1 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_3_1 (m : Nat) :
    stoppingTime (2 ^ 3 * m + 1) 3 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_3_1 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_3_1 : oddCount 1 3 = 2 ∧ acceleratedOrbit 3 1 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_3_1 (m : Nat) :
    acceleratedOrbit 3 (2 ^ 3 * m + 1) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_3_1.1, data_3_1.2]

/-- Complete interval computation for depth 3, residue 2. -/
theorem bounds_3_2 : exactInterval 3 2 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_3_2 (m : Nat) :
    stoppingTime (2 ^ 3 * m + 2) 3 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_3_2 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_3_2 : oddCount 2 3 = 1 ∧ acceleratedOrbit 3 2 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_3_2 (m : Nat) :
    acceleratedOrbit 3 (2 ^ 3 * m + 2) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_3_2.1, data_3_2.2]

/-- Complete interval computation for depth 3, residue 3. -/
theorem bounds_3_3 : exactInterval 3 3 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_3_3 (m : Nat) :
    stoppingTime (2 ^ 3 * m + 3) 3 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_3_3 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_3_3 : oddCount 3 3 = 2 ∧ acceleratedOrbit 3 3 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_3_3 (m : Nat) :
    acceleratedOrbit 3 (2 ^ 3 * m + 3) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_3_3.1, data_3_3.2]

end Collatz.Research.DescentIntervals.Batch001
