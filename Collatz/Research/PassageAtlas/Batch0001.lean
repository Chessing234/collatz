import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0001

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 0. -/
theorem bounds_15_0 : exactInterval 15 0 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_0 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 0) 15 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_0 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_0 : oddCount 0 15 = 0 ∧ acceleratedOrbit 15 0 = 0 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_0 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 0) = 3 ^ 0 * m + 0 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_0.1, data_15_0.2]

/-- Complete interval computation for depth 15, residue 1. -/
theorem bounds_15_1 : exactInterval 15 1 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1) 15 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1 : oddCount 1 15 = 8 ∧ acceleratedOrbit 15 1 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1) = 3 ^ 8 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1.1, data_15_1.2]

/-- Complete interval computation for depth 15, residue 2. -/
theorem bounds_15_2 : exactInterval 15 2 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2 : oddCount 2 15 = 7 ∧ acceleratedOrbit 15 2 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2) = 3 ^ 7 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2.1, data_15_2.2]

/-- Complete interval computation for depth 15, residue 3. -/
theorem bounds_15_3 : exactInterval 15 3 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3 : oddCount 3 15 = 7 ∧ acceleratedOrbit 15 3 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3) = 3 ^ 7 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3.1, data_15_3.2]

/-- Complete interval computation for depth 15, residue 4. -/
theorem bounds_15_4 : exactInterval 15 4 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4 : oddCount 4 15 = 7 ∧ acceleratedOrbit 15 4 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4) = 3 ^ 7 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4.1, data_15_4.2]

/-- Complete interval computation for depth 15, residue 5. -/
theorem bounds_15_5 : exactInterval 15 5 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5 : oddCount 5 15 = 7 ∧ acceleratedOrbit 15 5 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5) = 3 ^ 7 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5.1, data_15_5.2]

/-- Complete interval computation for depth 15, residue 6. -/
theorem bounds_15_6 : exactInterval 15 6 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6 : oddCount 6 15 = 7 ∧ acceleratedOrbit 15 6 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6) = 3 ^ 7 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6.1, data_15_6.2]

/-- Complete interval computation for depth 15, residue 7. -/
theorem bounds_15_7 : exactInterval 15 7 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7 : oddCount 7 15 = 7 ∧ acceleratedOrbit 15 7 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7) = 3 ^ 7 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7.1, data_15_7.2]

/-- Complete interval computation for depth 15, residue 8. -/
theorem bounds_15_8 : exactInterval 15 8 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8 : oddCount 8 15 = 6 ∧ acceleratedOrbit 15 8 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8) = 3 ^ 6 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8.1, data_15_8.2]

/-- Complete interval computation for depth 15, residue 9. -/
theorem bounds_15_9 : exactInterval 15 9 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9 : oddCount 9 15 = 7 ∧ acceleratedOrbit 15 9 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9) = 3 ^ 7 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9.1, data_15_9.2]

/-- Complete interval computation for depth 15, residue 10. -/
theorem bounds_15_10 : exactInterval 15 10 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10 : oddCount 10 15 = 6 ∧ acceleratedOrbit 15 10 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10) = 3 ^ 6 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10.1, data_15_10.2]

/-- Complete interval computation for depth 15, residue 11. -/
theorem bounds_15_11 : exactInterval 15 11 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11 : oddCount 11 15 = 7 ∧ acceleratedOrbit 15 11 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11) = 3 ^ 7 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11.1, data_15_11.2]

/-- Complete interval computation for depth 15, residue 12. -/
theorem bounds_15_12 : exactInterval 15 12 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12 : oddCount 12 15 = 6 ∧ acceleratedOrbit 15 12 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12) = 3 ^ 6 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12.1, data_15_12.2]

/-- Complete interval computation for depth 15, residue 13. -/
theorem bounds_15_13 : exactInterval 15 13 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13 : oddCount 13 15 = 6 ∧ acceleratedOrbit 15 13 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13) = 3 ^ 6 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13.1, data_15_13.2]

/-- Complete interval computation for depth 15, residue 14. -/
theorem bounds_15_14 : exactInterval 15 14 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14 : oddCount 14 15 = 7 ∧ acceleratedOrbit 15 14 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14) = 3 ^ 7 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14.1, data_15_14.2]

/-- Complete interval computation for depth 15, residue 15. -/
theorem bounds_15_15 : exactInterval 15 15 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15 : oddCount 15 15 = 7 ∧ acceleratedOrbit 15 15 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15) = 3 ^ 7 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15.1, data_15_15.2]

/-- Complete interval computation for depth 15, residue 16. -/
theorem bounds_15_16 : exactInterval 15 16 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16 : oddCount 16 15 = 6 ∧ acceleratedOrbit 15 16 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16.1, data_15_16.2]

/-- Complete interval computation for depth 15, residue 17. -/
theorem bounds_15_17 : exactInterval 15 17 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17 : oddCount 17 15 = 6 ∧ acceleratedOrbit 15 17 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17) = 3 ^ 6 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17.1, data_15_17.2]

/-- Complete interval computation for depth 15, residue 18. -/
theorem bounds_15_18 : exactInterval 15 18 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18 : oddCount 18 15 = 7 ∧ acceleratedOrbit 15 18 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18) = 3 ^ 7 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18.1, data_15_18.2]

/-- Complete interval computation for depth 15, residue 19. -/
theorem bounds_15_19 : exactInterval 15 19 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19 : oddCount 19 15 = 7 ∧ acceleratedOrbit 15 19 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19) = 3 ^ 7 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19.1, data_15_19.2]

/-- Complete interval computation for depth 15, residue 20. -/
theorem bounds_15_20 : exactInterval 15 20 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20 : oddCount 20 15 = 6 ∧ acceleratedOrbit 15 20 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20.1, data_15_20.2]

/-- Complete interval computation for depth 15, residue 21. -/
theorem bounds_15_21 : exactInterval 15 21 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21 : oddCount 21 15 = 6 ∧ acceleratedOrbit 15 21 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21.1, data_15_21.2]

/-- Complete interval computation for depth 15, residue 22. -/
theorem bounds_15_22 : exactInterval 15 22 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22 : oddCount 22 15 = 6 ∧ acceleratedOrbit 15 22 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22) = 3 ^ 6 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22.1, data_15_22.2]

/-- Complete interval computation for depth 15, residue 23. -/
theorem bounds_15_23 : exactInterval 15 23 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23 : oddCount 23 15 = 6 ∧ acceleratedOrbit 15 23 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23) = 3 ^ 6 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23.1, data_15_23.2]

/-- Complete interval computation for depth 15, residue 24. -/
theorem bounds_15_24 : exactInterval 15 24 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24 : oddCount 24 15 = 6 ∧ acceleratedOrbit 15 24 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24.1, data_15_24.2]

/-- Complete interval computation for depth 15, residue 25. -/
theorem bounds_15_25 : exactInterval 15 25 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25 : oddCount 25 15 = 7 ∧ acceleratedOrbit 15 25 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25) = 3 ^ 7 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25.1, data_15_25.2]

/-- Complete interval computation for depth 15, residue 26. -/
theorem bounds_15_26 : exactInterval 15 26 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26 : oddCount 26 15 = 6 ∧ acceleratedOrbit 15 26 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26.1, data_15_26.2]

/-- Complete interval computation for depth 15, residue 27. -/
theorem bounds_15_27 : exactInterval 15 27 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27 : oddCount 27 15 = 11 ∧ acceleratedOrbit 15 27 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27) = 3 ^ 11 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27.1, data_15_27.2]

/-- Complete interval computation for depth 15, residue 28. -/
theorem bounds_15_28 : exactInterval 15 28 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28 : oddCount 28 15 = 6 ∧ acceleratedOrbit 15 28 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28) = 3 ^ 6 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28.1, data_15_28.2]

/-- Complete interval computation for depth 15, residue 29. -/
theorem bounds_15_29 : exactInterval 15 29 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29 : oddCount 29 15 = 6 ∧ acceleratedOrbit 15 29 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29) = 3 ^ 6 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29.1, data_15_29.2]

/-- Complete interval computation for depth 15, residue 30. -/
theorem bounds_15_30 : exactInterval 15 30 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30 : oddCount 30 15 = 6 ∧ acceleratedOrbit 15 30 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30) = 3 ^ 6 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30.1, data_15_30.2]

/-- Complete interval computation for depth 15, residue 31. -/
theorem bounds_15_31 : exactInterval 15 31 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31 : oddCount 31 15 = 11 ∧ acceleratedOrbit 15 31 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31) = 3 ^ 11 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31.1, data_15_31.2]

end Collatz.Research.PassageAtlas.Batch0001
