import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0001

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 0. -/
theorem bounds_10_0 : exactInterval 10 0 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_0 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 0) 10 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_0 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_0 : oddCount 0 10 = 0 ∧ acceleratedOrbit 10 0 = 0 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_0 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 0) = 3 ^ 0 * m + 0 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_0.1, data_10_0.2]

/-- Complete interval computation for depth 10, residue 1. -/
theorem bounds_10_1 : exactInterval 10 1 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1) 10 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1 : oddCount 1 10 = 5 ∧ acceleratedOrbit 10 1 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1.1, data_10_1.2]

/-- Complete interval computation for depth 10, residue 2. -/
theorem bounds_10_2 : exactInterval 10 2 = ⟨1, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_2 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 2) 10 ↔ 1 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_2 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_2 : oddCount 2 10 = 5 ∧ acceleratedOrbit 10 2 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_2 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 2) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_2.1, data_10_2.2]

/-- Complete interval computation for depth 10, residue 3. -/
theorem bounds_10_3 : exactInterval 10 3 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_3 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 3) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_3 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_3 : oddCount 3 10 = 5 ∧ acceleratedOrbit 10 3 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_3 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 3) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_3.1, data_10_3.2]

/-- Complete interval computation for depth 10, residue 4. -/
theorem bounds_10_4 : exactInterval 10 4 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_4 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 4) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_4 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_4 : oddCount 4 10 = 4 ∧ acceleratedOrbit 10 4 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_4 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 4) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_4.1, data_10_4.2]

/-- Complete interval computation for depth 10, residue 5. -/
theorem bounds_10_5 : exactInterval 10 5 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_5 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 5) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_5 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_5 : oddCount 5 10 = 4 ∧ acceleratedOrbit 10 5 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_5 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 5) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_5.1, data_10_5.2]

/-- Complete interval computation for depth 10, residue 6. -/
theorem bounds_10_6 : exactInterval 10 6 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_6 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 6) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_6 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_6 : oddCount 6 10 = 4 ∧ acceleratedOrbit 10 6 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_6 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 6) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_6.1, data_10_6.2]

/-- Complete interval computation for depth 10, residue 7. -/
theorem bounds_10_7 : exactInterval 10 7 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_7 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 7) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_7 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_7 : oddCount 7 10 = 5 ∧ acceleratedOrbit 10 7 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_7 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 7) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_7.1, data_10_7.2]

/-- Complete interval computation for depth 10, residue 8. -/
theorem bounds_10_8 : exactInterval 10 8 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_8 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 8) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_8 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_8 : oddCount 8 10 = 4 ∧ acceleratedOrbit 10 8 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_8 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 8) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_8.1, data_10_8.2]

/-- Complete interval computation for depth 10, residue 9. -/
theorem bounds_10_9 : exactInterval 10 9 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_9 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 9) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_9 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_9 : oddCount 9 10 = 6 ∧ acceleratedOrbit 10 9 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_9 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 9) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_9.1, data_10_9.2]

/-- Complete interval computation for depth 10, residue 10. -/
theorem bounds_10_10 : exactInterval 10 10 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_10 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 10) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_10 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_10 : oddCount 10 10 = 4 ∧ acceleratedOrbit 10 10 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_10 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 10) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_10.1, data_10_10.2]

/-- Complete interval computation for depth 10, residue 11. -/
theorem bounds_10_11 : exactInterval 10 11 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_11 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 11) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_11 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_11 : oddCount 11 10 = 4 ∧ acceleratedOrbit 10 11 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_11 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 11) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_11.1, data_10_11.2]

/-- Complete interval computation for depth 10, residue 12. -/
theorem bounds_10_12 : exactInterval 10 12 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_12 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 12) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_12 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_12 : oddCount 12 10 = 4 ∧ acceleratedOrbit 10 12 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_12 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 12) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_12.1, data_10_12.2]

/-- Complete interval computation for depth 10, residue 13. -/
theorem bounds_10_13 : exactInterval 10 13 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_13 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 13) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_13 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_13 : oddCount 13 10 = 4 ∧ acceleratedOrbit 10 13 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_13 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 13) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_13.1, data_10_13.2]

/-- Complete interval computation for depth 10, residue 14. -/
theorem bounds_10_14 : exactInterval 10 14 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_14 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 14) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_14 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_14 : oddCount 14 10 = 5 ∧ acceleratedOrbit 10 14 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_14 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 14) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_14.1, data_10_14.2]

end Collatz.Research.StoppingAtlas.Batch0001
