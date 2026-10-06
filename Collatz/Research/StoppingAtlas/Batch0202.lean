import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0202

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 15. -/
theorem bounds_12_15 : exactInterval 12 15 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_15 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 15) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_15 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_15 : oddCount 15 12 = 5 ∧ acceleratedOrbit 12 15 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_15 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 15) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_15.1, data_12_15.2]

/-- Complete interval computation for depth 12, residue 16. -/
theorem bounds_12_16 : exactInterval 12 16 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_16 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 16) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_16 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_16 : oddCount 16 12 = 4 ∧ acceleratedOrbit 12 16 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_16 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 16) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_16.1, data_12_16.2]

/-- Complete interval computation for depth 12, residue 17. -/
theorem bounds_12_17 : exactInterval 12 17 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_17 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 17) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_17 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_17 : oddCount 17 12 = 5 ∧ acceleratedOrbit 12 17 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_17 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 17) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_17.1, data_12_17.2]

/-- Complete interval computation for depth 12, residue 18. -/
theorem bounds_12_18 : exactInterval 12 18 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_18 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 18) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_18 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_18 : oddCount 18 12 = 6 ∧ acceleratedOrbit 12 18 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_18 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 18) = 3 ^ 6 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_18.1, data_12_18.2]

/-- Complete interval computation for depth 12, residue 19. -/
theorem bounds_12_19 : exactInterval 12 19 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_19 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 19) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_19 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_19 : oddCount 19 12 = 6 ∧ acceleratedOrbit 12 19 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_19 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 19) = 3 ^ 6 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_19.1, data_12_19.2]

/-- Complete interval computation for depth 12, residue 20. -/
theorem bounds_12_20 : exactInterval 12 20 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_20 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 20) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_20 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_20 : oddCount 20 12 = 4 ∧ acceleratedOrbit 12 20 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_20 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 20) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_20.1, data_12_20.2]

/-- Complete interval computation for depth 12, residue 21. -/
theorem bounds_12_21 : exactInterval 12 21 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_21 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 21) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_21 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_21 : oddCount 21 12 = 4 ∧ acceleratedOrbit 12 21 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_21 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 21) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_21.1, data_12_21.2]

/-- Complete interval computation for depth 12, residue 22. -/
theorem bounds_12_22 : exactInterval 12 22 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_22 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 22) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_22 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_22 : oddCount 22 12 = 5 ∧ acceleratedOrbit 12 22 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_22 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 22) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_22.1, data_12_22.2]

/-- Complete interval computation for depth 12, residue 23. -/
theorem bounds_12_23 : exactInterval 12 23 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_23 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 23) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_23 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_23 : oddCount 23 12 = 5 ∧ acceleratedOrbit 12 23 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_23 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 23) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_23.1, data_12_23.2]

/-- Complete interval computation for depth 12, residue 24. -/
theorem bounds_12_24 : exactInterval 12 24 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_24 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 24) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_24 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_24 : oddCount 24 12 = 4 ∧ acceleratedOrbit 12 24 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_24 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 24) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_24.1, data_12_24.2]

/-- Complete interval computation for depth 12, residue 25. -/
theorem bounds_12_25 : exactInterval 12 25 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_25 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 25) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_25 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_25 : oddCount 25 12 = 6 ∧ acceleratedOrbit 12 25 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_25 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 25) = 3 ^ 6 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_25.1, data_12_25.2]

/-- Complete interval computation for depth 12, residue 26. -/
theorem bounds_12_26 : exactInterval 12 26 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_26 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 26) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_26 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_26 : oddCount 26 12 = 4 ∧ acceleratedOrbit 12 26 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_26 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 26) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_26.1, data_12_26.2]

/-- Complete interval computation for depth 12, residue 27. -/
theorem bounds_12_27 : exactInterval 12 27 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_27 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 27) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_27 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_27 : oddCount 27 12 = 9 ∧ acceleratedOrbit 12 27 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_27 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 27) = 3 ^ 9 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_27.1, data_12_27.2]

/-- Complete interval computation for depth 12, residue 28. -/
theorem bounds_12_28 : exactInterval 12 28 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_28 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 28) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_28 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_28 : oddCount 28 12 = 5 ∧ acceleratedOrbit 12 28 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_28 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 28) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_28.1, data_12_28.2]

/-- Complete interval computation for depth 12, residue 29. -/
theorem bounds_12_29 : exactInterval 12 29 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_29 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 29) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_29 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_29 : oddCount 29 12 = 5 ∧ acceleratedOrbit 12 29 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_29 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 29) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_29.1, data_12_29.2]

end Collatz.Research.StoppingAtlas.Batch0202
