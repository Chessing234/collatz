import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0201

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 0. -/
theorem bounds_12_0 : exactInterval 12 0 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_0 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 0) 12 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_0 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_0 : oddCount 0 12 = 0 ∧ acceleratedOrbit 12 0 = 0 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_0 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 0) = 3 ^ 0 * m + 0 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_0.1, data_12_0.2]

/-- Complete interval computation for depth 12, residue 1. -/
theorem bounds_12_1 : exactInterval 12 1 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1) 12 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1 : oddCount 1 12 = 6 ∧ acceleratedOrbit 12 1 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1) = 3 ^ 6 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1.1, data_12_1.2]

/-- Complete interval computation for depth 12, residue 2. -/
theorem bounds_12_2 : exactInterval 12 2 = ⟨1, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2) 12 ↔ 1 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2 : oddCount 2 12 = 6 ∧ acceleratedOrbit 12 2 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2.1, data_12_2.2]

/-- Complete interval computation for depth 12, residue 3. -/
theorem bounds_12_3 : exactInterval 12 3 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3 : oddCount 3 12 = 6 ∧ acceleratedOrbit 12 3 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3.1, data_12_3.2]

/-- Complete interval computation for depth 12, residue 4. -/
theorem bounds_12_4 : exactInterval 12 4 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4 : oddCount 4 12 = 5 ∧ acceleratedOrbit 12 4 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4.1, data_12_4.2]

/-- Complete interval computation for depth 12, residue 5. -/
theorem bounds_12_5 : exactInterval 12 5 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_5 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 5) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_5 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_5 : oddCount 5 12 = 5 ∧ acceleratedOrbit 12 5 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_5 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 5) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_5.1, data_12_5.2]

/-- Complete interval computation for depth 12, residue 6. -/
theorem bounds_12_6 : exactInterval 12 6 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_6 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 6) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_6 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_6 : oddCount 6 12 = 5 ∧ acceleratedOrbit 12 6 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_6 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 6) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_6.1, data_12_6.2]

/-- Complete interval computation for depth 12, residue 7. -/
theorem bounds_12_7 : exactInterval 12 7 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_7 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 7) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_7 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_7 : oddCount 7 12 = 6 ∧ acceleratedOrbit 12 7 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_7 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 7) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_7.1, data_12_7.2]

/-- Complete interval computation for depth 12, residue 8. -/
theorem bounds_12_8 : exactInterval 12 8 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_8 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 8) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_8 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_8 : oddCount 8 12 = 5 ∧ acceleratedOrbit 12 8 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_8 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 8) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_8.1, data_12_8.2]

/-- Complete interval computation for depth 12, residue 9. -/
theorem bounds_12_9 : exactInterval 12 9 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_9 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 9) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_9 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_9 : oddCount 9 12 = 6 ∧ acceleratedOrbit 12 9 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_9 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 9) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_9.1, data_12_9.2]

/-- Complete interval computation for depth 12, residue 10. -/
theorem bounds_12_10 : exactInterval 12 10 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_10 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 10) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_10 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_10 : oddCount 10 12 = 5 ∧ acceleratedOrbit 12 10 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_10 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 10) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_10.1, data_12_10.2]

/-- Complete interval computation for depth 12, residue 11. -/
theorem bounds_12_11 : exactInterval 12 11 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_11 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 11) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_11 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_11 : oddCount 11 12 = 5 ∧ acceleratedOrbit 12 11 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_11 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 11) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_11.1, data_12_11.2]

/-- Complete interval computation for depth 12, residue 12. -/
theorem bounds_12_12 : exactInterval 12 12 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_12 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 12) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_12 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_12 : oddCount 12 12 = 5 ∧ acceleratedOrbit 12 12 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_12 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 12) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_12.1, data_12_12.2]

/-- Complete interval computation for depth 12, residue 13. -/
theorem bounds_12_13 : exactInterval 12 13 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_13 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 13) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_13 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_13 : oddCount 13 12 = 5 ∧ acceleratedOrbit 12 13 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_13 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 13) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_13.1, data_12_13.2]

/-- Complete interval computation for depth 12, residue 14. -/
theorem bounds_12_14 : exactInterval 12 14 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_14 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 14) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_14 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_14 : oddCount 14 12 = 5 ∧ acceleratedOrbit 12 14 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_14 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 14) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_14.1, data_12_14.2]

end Collatz.Research.StoppingAtlas.Batch0201
