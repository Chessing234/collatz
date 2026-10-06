import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0002

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 15. -/
theorem bounds_10_15 : exactInterval 10 15 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_15 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 15) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_15 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_15 : oddCount 15 10 = 5 ∧ acceleratedOrbit 10 15 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_15 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 15) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_15.1, data_10_15.2]

/-- Complete interval computation for depth 10, residue 16. -/
theorem bounds_10_16 : exactInterval 10 16 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_16 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 16) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_16 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_16 : oddCount 16 10 = 3 ∧ acceleratedOrbit 10 16 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_16 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 16) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_16.1, data_10_16.2]

/-- Complete interval computation for depth 10, residue 17. -/
theorem bounds_10_17 : exactInterval 10 17 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_17 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 17) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_17 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_17 : oddCount 17 10 = 4 ∧ acceleratedOrbit 10 17 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_17 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 17) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_17.1, data_10_17.2]

/-- Complete interval computation for depth 10, residue 18. -/
theorem bounds_10_18 : exactInterval 10 18 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_18 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 18) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_18 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_18 : oddCount 18 10 = 5 ∧ acceleratedOrbit 10 18 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_18 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 18) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_18.1, data_10_18.2]

/-- Complete interval computation for depth 10, residue 19. -/
theorem bounds_10_19 : exactInterval 10 19 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_19 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 19) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_19 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_19 : oddCount 19 10 = 5 ∧ acceleratedOrbit 10 19 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_19 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 19) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_19.1, data_10_19.2]

/-- Complete interval computation for depth 10, residue 20. -/
theorem bounds_10_20 : exactInterval 10 20 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_20 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 20) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_20 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_20 : oddCount 20 10 = 3 ∧ acceleratedOrbit 10 20 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_20 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 20) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_20.1, data_10_20.2]

/-- Complete interval computation for depth 10, residue 21. -/
theorem bounds_10_21 : exactInterval 10 21 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_21 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 21) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_21 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_21 : oddCount 21 10 = 3 ∧ acceleratedOrbit 10 21 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_21 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 21) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_21.1, data_10_21.2]

/-- Complete interval computation for depth 10, residue 22. -/
theorem bounds_10_22 : exactInterval 10 22 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_22 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 22) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_22 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_22 : oddCount 22 10 = 4 ∧ acceleratedOrbit 10 22 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_22 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 22) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_22.1, data_10_22.2]

/-- Complete interval computation for depth 10, residue 23. -/
theorem bounds_10_23 : exactInterval 10 23 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_23 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 23) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_23 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_23 : oddCount 23 10 = 4 ∧ acceleratedOrbit 10 23 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_23 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 23) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_23.1, data_10_23.2]

/-- Complete interval computation for depth 10, residue 24. -/
theorem bounds_10_24 : exactInterval 10 24 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_24 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 24) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_24 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_24 : oddCount 24 10 = 3 ∧ acceleratedOrbit 10 24 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_24 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 24) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_24.1, data_10_24.2]

/-- Complete interval computation for depth 10, residue 25. -/
theorem bounds_10_25 : exactInterval 10 25 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_25 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 25) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_25 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_25 : oddCount 25 10 = 6 ∧ acceleratedOrbit 10 25 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_25 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 25) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_25.1, data_10_25.2]

/-- Complete interval computation for depth 10, residue 26. -/
theorem bounds_10_26 : exactInterval 10 26 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_26 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 26) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_26 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_26 : oddCount 26 10 = 3 ∧ acceleratedOrbit 10 26 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_26 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 26) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_26.1, data_10_26.2]

/-- Complete interval computation for depth 10, residue 27. -/
theorem bounds_10_27 : exactInterval 10 27 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_27 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 27) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_27 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_27 : oddCount 27 10 = 8 ∧ acceleratedOrbit 10 27 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_27 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 27) = 3 ^ 8 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_27.1, data_10_27.2]

/-- Complete interval computation for depth 10, residue 28. -/
theorem bounds_10_28 : exactInterval 10 28 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_28 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 28) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_28 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_28 : oddCount 28 10 = 5 ∧ acceleratedOrbit 10 28 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_28 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 28) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_28.1, data_10_28.2]

/-- Complete interval computation for depth 10, residue 29. -/
theorem bounds_10_29 : exactInterval 10 29 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_29 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 29) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_29 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_29 : oddCount 29 10 = 5 ∧ acceleratedOrbit 10 29 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_29 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 29) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_29.1, data_10_29.2]

end Collatz.Research.StoppingAtlas.Batch0002
