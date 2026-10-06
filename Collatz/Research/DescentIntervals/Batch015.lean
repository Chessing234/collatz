import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch015

/-- Complete interval computation for depth 7, residue 17. -/
theorem bounds_7_17 : exactInterval 7 17 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_17 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 17) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_17 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_17 : oddCount 17 7 = 3 ∧ acceleratedOrbit 7 17 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_17 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 17) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_17.1, data_7_17.2]

/-- Complete interval computation for depth 7, residue 18. -/
theorem bounds_7_18 : exactInterval 7 18 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_18 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 18) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_18 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_18 : oddCount 18 7 = 4 ∧ acceleratedOrbit 7 18 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_18 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 18) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_18.1, data_7_18.2]

/-- Complete interval computation for depth 7, residue 19. -/
theorem bounds_7_19 : exactInterval 7 19 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_19 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 19) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_19 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_19 : oddCount 19 7 = 4 ∧ acceleratedOrbit 7 19 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_19 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 19) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_19.1, data_7_19.2]

/-- Complete interval computation for depth 7, residue 20. -/
theorem bounds_7_20 : exactInterval 7 20 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_20 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 20) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_20 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_20 : oddCount 20 7 = 2 ∧ acceleratedOrbit 7 20 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_20 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 20) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_20.1, data_7_20.2]

/-- Complete interval computation for depth 7, residue 21. -/
theorem bounds_7_21 : exactInterval 7 21 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_21 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 21) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_21 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_21 : oddCount 21 7 = 2 ∧ acceleratedOrbit 7 21 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_21 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 21) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_21.1, data_7_21.2]

/-- Complete interval computation for depth 7, residue 22. -/
theorem bounds_7_22 : exactInterval 7 22 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_22 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 22) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_22 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_22 : oddCount 22 7 = 3 ∧ acceleratedOrbit 7 22 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_22 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 22) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_22.1, data_7_22.2]

/-- Complete interval computation for depth 7, residue 23. -/
theorem bounds_7_23 : exactInterval 7 23 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_23 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 23) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_23 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_23 : oddCount 23 7 = 3 ∧ acceleratedOrbit 7 23 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_23 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 23) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_23.1, data_7_23.2]

/-- Complete interval computation for depth 7, residue 24. -/
theorem bounds_7_24 : exactInterval 7 24 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_24 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 24) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_24 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_24 : oddCount 24 7 = 2 ∧ acceleratedOrbit 7 24 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_24 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 24) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_24.1, data_7_24.2]

/-- Complete interval computation for depth 7, residue 25. -/
theorem bounds_7_25 : exactInterval 7 25 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_25 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 25) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_25 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_25 : oddCount 25 7 = 4 ∧ acceleratedOrbit 7 25 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_25 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 25) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_25.1, data_7_25.2]

/-- Complete interval computation for depth 7, residue 26. -/
theorem bounds_7_26 : exactInterval 7 26 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_26 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 26) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_26 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_26 : oddCount 26 7 = 2 ∧ acceleratedOrbit 7 26 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_26 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 26) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_26.1, data_7_26.2]

end Collatz.Research.DescentIntervals.Batch015
