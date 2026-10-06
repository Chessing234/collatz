import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0888

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6456. -/
theorem bounds_13_6456 : exactInterval 13 6456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6456 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6456) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6456 : oddCount 6456 13 = 7 ∧ acceleratedOrbit 13 6456 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6456 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6456) = 3 ^ 7 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6456.1, data_13_6456.2]

/-- Complete interval computation for depth 13, residue 6457. -/
theorem bounds_13_6457 : exactInterval 13 6457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6457 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6457) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6457 : oddCount 6457 13 = 8 ∧ acceleratedOrbit 13 6457 = 5174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6457 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6457) = 3 ^ 8 * m + 5174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6457.1, data_13_6457.2]

/-- Complete interval computation for depth 13, residue 6458. -/
theorem bounds_13_6458 : exactInterval 13 6458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6458 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6458) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6458 : oddCount 6458 13 = 7 ∧ acceleratedOrbit 13 6458 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6458 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6458) = 3 ^ 7 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6458.1, data_13_6458.2]

/-- Complete interval computation for depth 13, residue 6459. -/
theorem bounds_13_6459 : exactInterval 13 6459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6459 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6459) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6459 : oddCount 6459 13 = 7 ∧ acceleratedOrbit 13 6459 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6459 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6459) = 3 ^ 7 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6459.1, data_13_6459.2]

/-- Complete interval computation for depth 13, residue 6460. -/
theorem bounds_13_6460 : exactInterval 13 6460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6460 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6460) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6460 : oddCount 6460 13 = 7 ∧ acceleratedOrbit 13 6460 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6460 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6460) = 3 ^ 7 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6460.1, data_13_6460.2]

/-- Complete interval computation for depth 13, residue 6461. -/
theorem bounds_13_6461 : exactInterval 13 6461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6461 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6461) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6461 : oddCount 6461 13 = 7 ∧ acceleratedOrbit 13 6461 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6461 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6461) = 3 ^ 7 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6461.1, data_13_6461.2]

/-- Complete interval computation for depth 13, residue 6462. -/
theorem bounds_13_6462 : exactInterval 13 6462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6462 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6462) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6462 : oddCount 6462 13 = 10 ∧ acceleratedOrbit 13 6462 = 46595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6462 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6462) = 3 ^ 10 * m + 46595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6462.1, data_13_6462.2]

/-- Complete interval computation for depth 13, residue 6463. -/
theorem bounds_13_6463 : exactInterval 13 6463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6463 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6463) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6463 : oddCount 6463 13 = 10 ∧ acceleratedOrbit 13 6463 = 46595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6463 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6463) = 3 ^ 10 * m + 46595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6463.1, data_13_6463.2]

/-- Complete interval computation for depth 13, residue 6464. -/
theorem bounds_13_6464 : exactInterval 13 6464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6464 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6464) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6464 : oddCount 6464 13 = 3 ∧ acceleratedOrbit 13 6464 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6464 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6464) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6464.1, data_13_6464.2]

/-- Complete interval computation for depth 13, residue 6465. -/
theorem bounds_13_6465 : exactInterval 13 6465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6465 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6465) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6465 : oddCount 6465 13 = 4 ∧ acceleratedOrbit 13 6465 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6465 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6465) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6465.1, data_13_6465.2]

/-- Complete interval computation for depth 13, residue 6466. -/
theorem bounds_13_6466 : exactInterval 13 6466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6466 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6466) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6466 : oddCount 6466 13 = 9 ∧ acceleratedOrbit 13 6466 = 15551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6466 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6466) = 3 ^ 9 * m + 15551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6466.1, data_13_6466.2]

/-- Complete interval computation for depth 13, residue 6467. -/
theorem bounds_13_6467 : exactInterval 13 6467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6467 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6467) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6467 : oddCount 6467 13 = 9 ∧ acceleratedOrbit 13 6467 = 15551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6467 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6467) = 3 ^ 9 * m + 15551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6467.1, data_13_6467.2]

/-- Complete interval computation for depth 13, residue 6468. -/
theorem bounds_13_6468 : exactInterval 13 6468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6468 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6468) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6468 : oddCount 6468 13 = 6 ∧ acceleratedOrbit 13 6468 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6468 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6468) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6468.1, data_13_6468.2]

/-- Complete interval computation for depth 13, residue 6469. -/
theorem bounds_13_6469 : exactInterval 13 6469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6469 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6469) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6469 : oddCount 6469 13 = 6 ∧ acceleratedOrbit 13 6469 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6469 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6469) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6469.1, data_13_6469.2]

/-- Complete interval computation for depth 13, residue 6470. -/
theorem bounds_13_6470 : exactInterval 13 6470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6470 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6470) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6470 : oddCount 6470 13 = 6 ∧ acceleratedOrbit 13 6470 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6470 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6470) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6470.1, data_13_6470.2]

end Collatz.Research.StoppingAtlas.Batch0888
