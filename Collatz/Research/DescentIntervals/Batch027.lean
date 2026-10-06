import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch027

/-- Complete interval computation for depth 8, residue 11. -/
theorem bounds_8_11 : exactInterval 8 11 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_11 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 11) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_11 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_11 : oddCount 11 8 = 4 ∧ acceleratedOrbit 8 11 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_11 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 11) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_11.1, data_8_11.2]

/-- Complete interval computation for depth 8, residue 12. -/
theorem bounds_8_12 : exactInterval 8 12 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_12 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 12) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_12 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_12 : oddCount 12 8 = 3 ∧ acceleratedOrbit 8 12 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_12 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 12) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_12.1, data_8_12.2]

/-- Complete interval computation for depth 8, residue 13. -/
theorem bounds_8_13 : exactInterval 8 13 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_13 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 13) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_13 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_13 : oddCount 13 8 = 3 ∧ acceleratedOrbit 8 13 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_13 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 13) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_13.1, data_8_13.2]

/-- Complete interval computation for depth 8, residue 14. -/
theorem bounds_8_14 : exactInterval 8 14 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_14 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 14) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_14 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_14 : oddCount 14 8 = 4 ∧ acceleratedOrbit 8 14 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_14 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 14) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_14.1, data_8_14.2]

/-- Complete interval computation for depth 8, residue 15. -/
theorem bounds_8_15 : exactInterval 8 15 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_15 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 15) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_15 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_15 : oddCount 15 8 = 4 ∧ acceleratedOrbit 8 15 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_15 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 15) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_15.1, data_8_15.2]

/-- Complete interval computation for depth 8, residue 16. -/
theorem bounds_8_16 : exactInterval 8 16 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_16 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 16) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_16 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_16 : oddCount 16 8 = 2 ∧ acceleratedOrbit 8 16 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_16 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 16) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_16.1, data_8_16.2]

/-- Complete interval computation for depth 8, residue 17. -/
theorem bounds_8_17 : exactInterval 8 17 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_17 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 17) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_17 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_17 : oddCount 17 8 = 3 ∧ acceleratedOrbit 8 17 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_17 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 17) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_17.1, data_8_17.2]

/-- Complete interval computation for depth 8, residue 18. -/
theorem bounds_8_18 : exactInterval 8 18 = ⟨1, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_18 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 18) 8 ↔ 1 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_18 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_18 : oddCount 18 8 = 5 ∧ acceleratedOrbit 8 18 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_18 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 18) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_18.1, data_8_18.2]

/-- Complete interval computation for depth 8, residue 19. -/
theorem bounds_8_19 : exactInterval 8 19 = ⟨1, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_19 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 19) 8 ↔ 1 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_19 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_19 : oddCount 19 8 = 5 ∧ acceleratedOrbit 8 19 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_19 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 19) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_19.1, data_8_19.2]

/-- Complete interval computation for depth 8, residue 20. -/
theorem bounds_8_20 : exactInterval 8 20 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_20 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 20) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_20 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_20 : oddCount 20 8 = 2 ∧ acceleratedOrbit 8 20 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_20 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 20) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_20.1, data_8_20.2]

end Collatz.Research.DescentIntervals.Batch027
