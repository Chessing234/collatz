import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch009

/-- Complete interval computation for depth 6, residue 19. -/
theorem bounds_6_19 : exactInterval 6 19 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_19 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 19) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_19 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_19 : oddCount 19 6 = 4 ∧ acceleratedOrbit 6 19 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_19 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 19) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_19.1, data_6_19.2]

/-- Complete interval computation for depth 6, residue 20. -/
theorem bounds_6_20 : exactInterval 6 20 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_20 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 20) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_20 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_20 : oddCount 20 6 = 1 ∧ acceleratedOrbit 6 20 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_20 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 20) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_20.1, data_6_20.2]

/-- Complete interval computation for depth 6, residue 21. -/
theorem bounds_6_21 : exactInterval 6 21 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_21 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 21) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_21 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_21 : oddCount 21 6 = 1 ∧ acceleratedOrbit 6 21 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_21 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 21) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_21.1, data_6_21.2]

/-- Complete interval computation for depth 6, residue 22. -/
theorem bounds_6_22 : exactInterval 6 22 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_22 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 22) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_22 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_22 : oddCount 22 6 = 3 ∧ acceleratedOrbit 6 22 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_22 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 22) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_22.1, data_6_22.2]

/-- Complete interval computation for depth 6, residue 23. -/
theorem bounds_6_23 : exactInterval 6 23 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_23 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 23) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_23 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_23 : oddCount 23 6 = 3 ∧ acceleratedOrbit 6 23 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_23 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 23) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_23.1, data_6_23.2]

/-- Complete interval computation for depth 6, residue 24. -/
theorem bounds_6_24 : exactInterval 6 24 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_24 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 24) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_24 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_24 : oddCount 24 6 = 2 ∧ acceleratedOrbit 6 24 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_24 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 24) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_24.1, data_6_24.2]

/-- Complete interval computation for depth 6, residue 25. -/
theorem bounds_6_25 : exactInterval 6 25 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_25 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 25) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_25 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_25 : oddCount 25 6 = 3 ∧ acceleratedOrbit 6 25 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_25 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 25) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_25.1, data_6_25.2]

/-- Complete interval computation for depth 6, residue 26. -/
theorem bounds_6_26 : exactInterval 6 26 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_26 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 26) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_26 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_26 : oddCount 26 6 = 2 ∧ acceleratedOrbit 6 26 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_26 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 26) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_26.1, data_6_26.2]

/-- Complete interval computation for depth 6, residue 27. -/
theorem bounds_6_27 : exactInterval 6 27 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_27 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 27) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_27 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_27 : oddCount 27 6 = 5 ∧ acceleratedOrbit 6 27 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_27 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 27) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_27.1, data_6_27.2]

/-- Complete interval computation for depth 6, residue 28. -/
theorem bounds_6_28 : exactInterval 6 28 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_6_28 (m : Nat) :
    stoppingTime (2 ^ 6 * m + 28) 6 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_6_28 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_6_28 : oddCount 28 6 = 3 ∧ acceleratedOrbit 6 28 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_6_28 (m : Nat) :
    acceleratedOrbit 6 (2 ^ 6 * m + 28) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_6_28.1, data_6_28.2]

end Collatz.Research.DescentIntervals.Batch009
