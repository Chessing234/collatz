import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0468

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5. -/
theorem bounds_13_5 : exactInterval 13 5 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5 : oddCount 5 13 = 6 ∧ acceleratedOrbit 13 5 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5.1, data_13_5.2]

/-- Complete interval computation for depth 13, residue 6. -/
theorem bounds_13_6 : exactInterval 13 6 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6 : oddCount 6 13 = 6 ∧ acceleratedOrbit 13 6 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6.1, data_13_6.2]

/-- Complete interval computation for depth 13, residue 7. -/
theorem bounds_13_7 : exactInterval 13 7 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7 : oddCount 7 13 = 6 ∧ acceleratedOrbit 13 7 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7) = 3 ^ 6 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7.1, data_13_7.2]

/-- Complete interval computation for depth 13, residue 8. -/
theorem bounds_13_8 : exactInterval 13 8 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8 : oddCount 8 13 = 5 ∧ acceleratedOrbit 13 8 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8.1, data_13_8.2]

/-- Complete interval computation for depth 13, residue 9. -/
theorem bounds_13_9 : exactInterval 13 9 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_9 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 9) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_9 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_9 : oddCount 9 13 = 6 ∧ acceleratedOrbit 13 9 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_9 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 9) = 3 ^ 6 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_9.1, data_13_9.2]

/-- Complete interval computation for depth 13, residue 10. -/
theorem bounds_13_10 : exactInterval 13 10 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_10 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 10) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_10 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_10 : oddCount 10 13 = 5 ∧ acceleratedOrbit 13 10 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_10 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 10) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_10.1, data_13_10.2]

/-- Complete interval computation for depth 13, residue 11. -/
theorem bounds_13_11 : exactInterval 13 11 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_11 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 11) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_11 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_11 : oddCount 11 13 = 6 ∧ acceleratedOrbit 13 11 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_11 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 11) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_11.1, data_13_11.2]

/-- Complete interval computation for depth 13, residue 12. -/
theorem bounds_13_12 : exactInterval 13 12 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_12 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 12) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_12 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_12 : oddCount 12 13 = 5 ∧ acceleratedOrbit 13 12 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_12 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 12) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_12.1, data_13_12.2]

/-- Complete interval computation for depth 13, residue 13. -/
theorem bounds_13_13 : exactInterval 13 13 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_13 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 13) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_13 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_13 : oddCount 13 13 = 5 ∧ acceleratedOrbit 13 13 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_13 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 13) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_13.1, data_13_13.2]

/-- Complete interval computation for depth 13, residue 14. -/
theorem bounds_13_14 : exactInterval 13 14 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_14 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 14) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_14 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_14 : oddCount 14 13 = 6 ∧ acceleratedOrbit 13 14 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_14 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 14) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_14.1, data_13_14.2]

/-- Complete interval computation for depth 13, residue 15. -/
theorem bounds_13_15 : exactInterval 13 15 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_15 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 15) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_15 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_15 : oddCount 15 13 = 6 ∧ acceleratedOrbit 13 15 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_15 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 15) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_15.1, data_13_15.2]

/-- Complete interval computation for depth 13, residue 16. -/
theorem bounds_13_16 : exactInterval 13 16 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_16 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 16) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_16 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_16 : oddCount 16 13 = 5 ∧ acceleratedOrbit 13 16 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_16 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 16) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_16.1, data_13_16.2]

/-- Complete interval computation for depth 13, residue 17. -/
theorem bounds_13_17 : exactInterval 13 17 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_17 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 17) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_17 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_17 : oddCount 17 13 = 5 ∧ acceleratedOrbit 13 17 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_17 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 17) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_17.1, data_13_17.2]

/-- Complete interval computation for depth 13, residue 18. -/
theorem bounds_13_18 : exactInterval 13 18 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_18 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 18) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_18 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_18 : oddCount 18 13 = 6 ∧ acceleratedOrbit 13 18 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_18 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 18) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_18.1, data_13_18.2]

/-- Complete interval computation for depth 13, residue 19. -/
theorem bounds_13_19 : exactInterval 13 19 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_19 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 19) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_19 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_19 : oddCount 19 13 = 6 ∧ acceleratedOrbit 13 19 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_19 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 19) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_19.1, data_13_19.2]

end Collatz.Research.StoppingAtlas.Batch0468
