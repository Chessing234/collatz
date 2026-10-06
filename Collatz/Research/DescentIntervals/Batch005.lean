import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch005

/-- Complete interval computation for depth 5, residue 10. -/
theorem bounds_5_10 : exactInterval 5 10 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_10 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 10) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_10 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_10 : oddCount 10 5 = 1 ∧ acceleratedOrbit 5 10 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_10 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 10) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_10.1, data_5_10.2]

/-- Complete interval computation for depth 5, residue 11. -/
theorem bounds_5_11 : exactInterval 5 11 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_11 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 11) 5 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_11 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_11 : oddCount 11 5 = 3 ∧ acceleratedOrbit 5 11 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_11 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 11) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_11.1, data_5_11.2]

/-- Complete interval computation for depth 5, residue 12. -/
theorem bounds_5_12 : exactInterval 5 12 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_12 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 12) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_12 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_12 : oddCount 12 5 = 2 ∧ acceleratedOrbit 5 12 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_12 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 12) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_12.1, data_5_12.2]

/-- Complete interval computation for depth 5, residue 13. -/
theorem bounds_5_13 : exactInterval 5 13 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_13 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 13) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_13 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_13 : oddCount 13 5 = 2 ∧ acceleratedOrbit 5 13 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_13 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 13) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_13.1, data_5_13.2]

/-- Complete interval computation for depth 5, residue 14. -/
theorem bounds_5_14 : exactInterval 5 14 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_14 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 14) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_14 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_14 : oddCount 14 5 = 3 ∧ acceleratedOrbit 5 14 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_14 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 14) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_14.1, data_5_14.2]

/-- Complete interval computation for depth 5, residue 15. -/
theorem bounds_5_15 : exactInterval 5 15 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_15 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 15) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_15 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_15 : oddCount 15 5 = 4 ∧ acceleratedOrbit 5 15 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_15 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 15) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_15.1, data_5_15.2]

/-- Complete interval computation for depth 5, residue 16. -/
theorem bounds_5_16 : exactInterval 5 16 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_16 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 16) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_16 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_16 : oddCount 16 5 = 1 ∧ acceleratedOrbit 5 16 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_16 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 16) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_16.1, data_5_16.2]

/-- Complete interval computation for depth 5, residue 17. -/
theorem bounds_5_17 : exactInterval 5 17 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_17 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 17) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_17 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_17 : oddCount 17 5 = 2 ∧ acceleratedOrbit 5 17 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_17 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 17) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_17.1, data_5_17.2]

/-- Complete interval computation for depth 5, residue 18. -/
theorem bounds_5_18 : exactInterval 5 18 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_18 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 18) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_18 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_18 : oddCount 18 5 = 3 ∧ acceleratedOrbit 5 18 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_18 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 18) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_18.1, data_5_18.2]

/-- Complete interval computation for depth 5, residue 19. -/
theorem bounds_5_19 : exactInterval 5 19 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_19 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 19) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_19 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_19 : oddCount 19 5 = 3 ∧ acceleratedOrbit 5 19 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_19 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 19) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_19.1, data_5_19.2]

/-- Complete interval computation for depth 5, residue 20. -/
theorem bounds_5_20 : exactInterval 5 20 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_5_20 (m : Nat) :
    stoppingTime (2 ^ 5 * m + 20) 5 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_5_20 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_5_20 : oddCount 20 5 = 1 ∧ acceleratedOrbit 5 20 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_5_20 (m : Nat) :
    acceleratedOrbit 5 (2 ^ 5 * m + 20) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_5_20.1, data_5_20.2]

end Collatz.Research.DescentIntervals.Batch005
