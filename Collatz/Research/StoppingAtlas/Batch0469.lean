import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0469

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 20. -/
theorem bounds_13_20 : exactInterval 13 20 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_20 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 20) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_20 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_20 : oddCount 20 13 = 5 ∧ acceleratedOrbit 13 20 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_20 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 20) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_20.1, data_13_20.2]

/-- Complete interval computation for depth 13, residue 21. -/
theorem bounds_13_21 : exactInterval 13 21 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_21 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 21) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_21 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_21 : oddCount 21 13 = 5 ∧ acceleratedOrbit 13 21 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_21 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 21) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_21.1, data_13_21.2]

/-- Complete interval computation for depth 13, residue 22. -/
theorem bounds_13_22 : exactInterval 13 22 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_22 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 22) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_22 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_22 : oddCount 22 13 = 5 ∧ acceleratedOrbit 13 22 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_22 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 22) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_22.1, data_13_22.2]

/-- Complete interval computation for depth 13, residue 23. -/
theorem bounds_13_23 : exactInterval 13 23 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_23 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 23) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_23 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_23 : oddCount 23 13 = 5 ∧ acceleratedOrbit 13 23 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_23 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 23) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_23.1, data_13_23.2]

/-- Complete interval computation for depth 13, residue 24. -/
theorem bounds_13_24 : exactInterval 13 24 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_24 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 24) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_24 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_24 : oddCount 24 13 = 5 ∧ acceleratedOrbit 13 24 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_24 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 24) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_24.1, data_13_24.2]

/-- Complete interval computation for depth 13, residue 25. -/
theorem bounds_13_25 : exactInterval 13 25 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_25 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 25) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_25 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_25 : oddCount 25 13 = 7 ∧ acceleratedOrbit 13 25 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_25 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 25) = 3 ^ 7 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_25.1, data_13_25.2]

/-- Complete interval computation for depth 13, residue 26. -/
theorem bounds_13_26 : exactInterval 13 26 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_26 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 26) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_26 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_26 : oddCount 26 13 = 5 ∧ acceleratedOrbit 13 26 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_26 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 26) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_26.1, data_13_26.2]

/-- Complete interval computation for depth 13, residue 27. -/
theorem bounds_13_27 : exactInterval 13 27 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_27 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 27) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_27 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_27 : oddCount 27 13 = 10 ∧ acceleratedOrbit 13 27 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_27 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 27) = 3 ^ 10 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_27.1, data_13_27.2]

/-- Complete interval computation for depth 13, residue 28. -/
theorem bounds_13_28 : exactInterval 13 28 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_28 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 28) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_28 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_28 : oddCount 28 13 = 5 ∧ acceleratedOrbit 13 28 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_28 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 28) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_28.1, data_13_28.2]

/-- Complete interval computation for depth 13, residue 29. -/
theorem bounds_13_29 : exactInterval 13 29 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_29 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 29) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_29 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_29 : oddCount 29 13 = 5 ∧ acceleratedOrbit 13 29 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_29 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 29) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_29.1, data_13_29.2]

/-- Complete interval computation for depth 13, residue 30. -/
theorem bounds_13_30 : exactInterval 13 30 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_30 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 30) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_30 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_30 : oddCount 30 13 = 5 ∧ acceleratedOrbit 13 30 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_30 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 30) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_30.1, data_13_30.2]

/-- Complete interval computation for depth 13, residue 31. -/
theorem bounds_13_31 : exactInterval 13 31 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_31 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 31) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_31 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_31 : oddCount 31 13 = 10 ∧ acceleratedOrbit 13 31 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_31 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 31) = 3 ^ 10 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_31.1, data_13_31.2]

/-- Complete interval computation for depth 13, residue 32. -/
theorem bounds_13_32 : exactInterval 13 32 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_32 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 32) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_32 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_32 : oddCount 32 13 = 4 ∧ acceleratedOrbit 13 32 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_32 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 32) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_32.1, data_13_32.2]

/-- Complete interval computation for depth 13, residue 33. -/
theorem bounds_13_33 : exactInterval 13 33 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_33 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 33) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_33 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_33 : oddCount 33 13 = 7 ∧ acceleratedOrbit 13 33 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_33 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 33) = 3 ^ 7 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_33.1, data_13_33.2]

/-- Complete interval computation for depth 13, residue 34. -/
theorem bounds_13_34 : exactInterval 13 34 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_34 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 34) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_34 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_34 : oddCount 34 13 = 5 ∧ acceleratedOrbit 13 34 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_34 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 34) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_34.1, data_13_34.2]

end Collatz.Research.StoppingAtlas.Batch0469
