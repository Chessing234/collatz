import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0068

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 5. -/
theorem bounds_11_5 : exactInterval 11 5 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_5 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 5) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_5 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_5 : oddCount 5 11 = 5 ∧ acceleratedOrbit 11 5 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_5 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 5) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_5.1, data_11_5.2]

/-- Complete interval computation for depth 11, residue 6. -/
theorem bounds_11_6 : exactInterval 11 6 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_6 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 6) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_6 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_6 : oddCount 6 11 = 5 ∧ acceleratedOrbit 11 6 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_6 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 6) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_6.1, data_11_6.2]

/-- Complete interval computation for depth 11, residue 7. -/
theorem bounds_11_7 : exactInterval 11 7 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_7 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 7) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_7 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_7 : oddCount 7 11 = 5 ∧ acceleratedOrbit 11 7 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_7 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 7) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_7.1, data_11_7.2]

/-- Complete interval computation for depth 11, residue 8. -/
theorem bounds_11_8 : exactInterval 11 8 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_8 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 8) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_8 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_8 : oddCount 8 11 = 4 ∧ acceleratedOrbit 11 8 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_8 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 8) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_8.1, data_11_8.2]

/-- Complete interval computation for depth 11, residue 9. -/
theorem bounds_11_9 : exactInterval 11 9 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_9 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 9) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_9 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_9 : oddCount 9 11 = 6 ∧ acceleratedOrbit 11 9 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_9 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 9) = 3 ^ 6 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_9.1, data_11_9.2]

/-- Complete interval computation for depth 11, residue 10. -/
theorem bounds_11_10 : exactInterval 11 10 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_10 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 10) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_10 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_10 : oddCount 10 11 = 4 ∧ acceleratedOrbit 11 10 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_10 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 10) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_10.1, data_11_10.2]

/-- Complete interval computation for depth 11, residue 11. -/
theorem bounds_11_11 : exactInterval 11 11 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_11 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 11) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_11 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_11 : oddCount 11 11 = 5 ∧ acceleratedOrbit 11 11 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_11 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 11) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_11.1, data_11_11.2]

/-- Complete interval computation for depth 11, residue 12. -/
theorem bounds_11_12 : exactInterval 11 12 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_12 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 12) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_12 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_12 : oddCount 12 11 = 4 ∧ acceleratedOrbit 11 12 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_12 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 12) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_12.1, data_11_12.2]

/-- Complete interval computation for depth 11, residue 13. -/
theorem bounds_11_13 : exactInterval 11 13 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_13 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 13) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_13 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_13 : oddCount 13 11 = 4 ∧ acceleratedOrbit 11 13 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_13 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 13) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_13.1, data_11_13.2]

/-- Complete interval computation for depth 11, residue 14. -/
theorem bounds_11_14 : exactInterval 11 14 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_14 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 14) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_14 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_14 : oddCount 14 11 = 5 ∧ acceleratedOrbit 11 14 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_14 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 14) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_14.1, data_11_14.2]

/-- Complete interval computation for depth 11, residue 15. -/
theorem bounds_11_15 : exactInterval 11 15 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_15 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 15) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_15 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_15 : oddCount 15 11 = 5 ∧ acceleratedOrbit 11 15 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_15 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 15) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_15.1, data_11_15.2]

/-- Complete interval computation for depth 11, residue 16. -/
theorem bounds_11_16 : exactInterval 11 16 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_16 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 16) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_16 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_16 : oddCount 16 11 = 4 ∧ acceleratedOrbit 11 16 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_16 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 16) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_16.1, data_11_16.2]

/-- Complete interval computation for depth 11, residue 17. -/
theorem bounds_11_17 : exactInterval 11 17 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_17 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 17) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_17 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_17 : oddCount 17 11 = 4 ∧ acceleratedOrbit 11 17 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_17 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 17) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_17.1, data_11_17.2]

/-- Complete interval computation for depth 11, residue 18. -/
theorem bounds_11_18 : exactInterval 11 18 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_18 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 18) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_18 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_18 : oddCount 18 11 = 6 ∧ acceleratedOrbit 11 18 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_18 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 18) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_18.1, data_11_18.2]

/-- Complete interval computation for depth 11, residue 19. -/
theorem bounds_11_19 : exactInterval 11 19 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_19 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 19) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_19 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_19 : oddCount 19 11 = 6 ∧ acceleratedOrbit 11 19 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_19 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 19) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_19.1, data_11_19.2]

end Collatz.Research.StoppingAtlas.Batch0068
