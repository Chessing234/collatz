import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0069

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 20. -/
theorem bounds_11_20 : exactInterval 11 20 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_20 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 20) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_20 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_20 : oddCount 20 11 = 4 ∧ acceleratedOrbit 11 20 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_20 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 20) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_20.1, data_11_20.2]

/-- Complete interval computation for depth 11, residue 21. -/
theorem bounds_11_21 : exactInterval 11 21 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_21 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 21) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_21 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_21 : oddCount 21 11 = 4 ∧ acceleratedOrbit 11 21 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_21 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 21) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_21.1, data_11_21.2]

/-- Complete interval computation for depth 11, residue 22. -/
theorem bounds_11_22 : exactInterval 11 22 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_22 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 22) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_22 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_22 : oddCount 22 11 = 4 ∧ acceleratedOrbit 11 22 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_22 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 22) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_22.1, data_11_22.2]

/-- Complete interval computation for depth 11, residue 23. -/
theorem bounds_11_23 : exactInterval 11 23 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_23 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 23) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_23 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_23 : oddCount 23 11 = 4 ∧ acceleratedOrbit 11 23 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_23 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 23) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_23.1, data_11_23.2]

/-- Complete interval computation for depth 11, residue 24. -/
theorem bounds_11_24 : exactInterval 11 24 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_24 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 24) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_24 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_24 : oddCount 24 11 = 4 ∧ acceleratedOrbit 11 24 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_24 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 24) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_24.1, data_11_24.2]

/-- Complete interval computation for depth 11, residue 25. -/
theorem bounds_11_25 : exactInterval 11 25 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_25 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 25) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_25 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_25 : oddCount 25 11 = 6 ∧ acceleratedOrbit 11 25 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_25 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 25) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_25.1, data_11_25.2]

/-- Complete interval computation for depth 11, residue 26. -/
theorem bounds_11_26 : exactInterval 11 26 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_26 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 26) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_26 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_26 : oddCount 26 11 = 4 ∧ acceleratedOrbit 11 26 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_26 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 26) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_26.1, data_11_26.2]

/-- Complete interval computation for depth 11, residue 27. -/
theorem bounds_11_27 : exactInterval 11 27 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_27 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 27) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_27 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_27 : oddCount 27 11 = 8 ∧ acceleratedOrbit 11 27 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_27 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 27) = 3 ^ 8 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_27.1, data_11_27.2]

/-- Complete interval computation for depth 11, residue 28. -/
theorem bounds_11_28 : exactInterval 11 28 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_28 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 28) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_28 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_28 : oddCount 28 11 = 5 ∧ acceleratedOrbit 11 28 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_28 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 28) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_28.1, data_11_28.2]

/-- Complete interval computation for depth 11, residue 29. -/
theorem bounds_11_29 : exactInterval 11 29 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_29 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 29) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_29 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_29 : oddCount 29 11 = 5 ∧ acceleratedOrbit 11 29 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_29 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 29) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_29.1, data_11_29.2]

/-- Complete interval computation for depth 11, residue 30. -/
theorem bounds_11_30 : exactInterval 11 30 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_30 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 30) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_30 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_30 : oddCount 30 11 = 5 ∧ acceleratedOrbit 11 30 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_30 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 30) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_30.1, data_11_30.2]

/-- Complete interval computation for depth 11, residue 31. -/
theorem bounds_11_31 : exactInterval 11 31 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_31 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 31) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_31 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_31 : oddCount 31 11 = 8 ∧ acceleratedOrbit 11 31 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_31 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 31) = 3 ^ 8 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_31.1, data_11_31.2]

/-- Complete interval computation for depth 11, residue 32. -/
theorem bounds_11_32 : exactInterval 11 32 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_32 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 32) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_32 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_32 : oddCount 32 11 = 3 ∧ acceleratedOrbit 11 32 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_32 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 32) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_32.1, data_11_32.2]

/-- Complete interval computation for depth 11, residue 33. -/
theorem bounds_11_33 : exactInterval 11 33 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_33 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 33) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_33 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_33 : oddCount 33 11 = 6 ∧ acceleratedOrbit 11 33 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_33 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 33) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_33.1, data_11_33.2]

/-- Complete interval computation for depth 11, residue 34. -/
theorem bounds_11_34 : exactInterval 11 34 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_34 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 34) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_34 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_34 : oddCount 34 11 = 4 ∧ acceleratedOrbit 11 34 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_34 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 34) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_34.1, data_11_34.2]

end Collatz.Research.StoppingAtlas.Batch0069
