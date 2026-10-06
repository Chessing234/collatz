import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0823

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5457. -/
theorem bounds_13_5457 : exactInterval 13 5457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5457 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5457) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5457 : oddCount 5457 13 = 10 ∧ acceleratedOrbit 13 5457 = 39365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5457 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5457) = 3 ^ 10 * m + 39365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5457.1, data_13_5457.2]

/-- Complete interval computation for depth 13, residue 5458. -/
theorem bounds_13_5458 : exactInterval 13 5458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5458 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5458) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5458 : oddCount 5458 13 = 11 ∧ acceleratedOrbit 13 5458 = 118097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5458 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5458) = 3 ^ 11 * m + 118097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5458.1, data_13_5458.2]

/-- Complete interval computation for depth 13, residue 5459. -/
theorem bounds_13_5459 : exactInterval 13 5459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5459 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5459) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5459 : oddCount 5459 13 = 11 ∧ acceleratedOrbit 13 5459 = 118097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5459 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5459) = 3 ^ 11 * m + 118097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5459.1, data_13_5459.2]

/-- Complete interval computation for depth 13, residue 5460. -/
theorem bounds_13_5460 : exactInterval 13 5460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5460 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5460) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5460 : oddCount 5460 13 = 1 ∧ acceleratedOrbit 13 5460 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5460 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5460) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5460.1, data_13_5460.2]

/-- Complete interval computation for depth 13, residue 5461. -/
theorem bounds_13_5461 : exactInterval 13 5461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5461 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5461) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5461 : oddCount 5461 13 = 1 ∧ acceleratedOrbit 13 5461 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5461 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5461) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5461.1, data_13_5461.2]

/-- Complete interval computation for depth 13, residue 5462. -/
theorem bounds_13_5462 : exactInterval 13 5462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5462 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5462) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5462 : oddCount 5462 13 = 7 ∧ acceleratedOrbit 13 5462 = 1460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5462 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5462) = 3 ^ 7 * m + 1460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5462.1, data_13_5462.2]

/-- Complete interval computation for depth 13, residue 5463. -/
theorem bounds_13_5463 : exactInterval 13 5463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5463 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5463) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5463 : oddCount 5463 13 = 7 ∧ acceleratedOrbit 13 5463 = 1460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5463 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5463) = 3 ^ 7 * m + 1460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5463.1, data_13_5463.2]

/-- Complete interval computation for depth 13, residue 5464. -/
theorem bounds_13_5464 : exactInterval 13 5464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5464 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5464) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5464 : oddCount 5464 13 = 6 ∧ acceleratedOrbit 13 5464 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5464 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5464) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5464.1, data_13_5464.2]

/-- Complete interval computation for depth 13, residue 5465. -/
theorem bounds_13_5465 : exactInterval 13 5465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5465 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5465) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5465 : oddCount 5465 13 = 6 ∧ acceleratedOrbit 13 5465 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5465 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5465) = 3 ^ 6 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5465.1, data_13_5465.2]

/-- Complete interval computation for depth 13, residue 5466. -/
theorem bounds_13_5466 : exactInterval 13 5466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5466 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5466) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5466 : oddCount 5466 13 = 6 ∧ acceleratedOrbit 13 5466 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5466 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5466) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5466.1, data_13_5466.2]

/-- Complete interval computation for depth 13, residue 5467. -/
theorem bounds_13_5467 : exactInterval 13 5467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5467 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5467) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5467 : oddCount 5467 13 = 7 ∧ acceleratedOrbit 13 5467 = 1460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5467 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5467) = 3 ^ 7 * m + 1460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5467.1, data_13_5467.2]

/-- Complete interval computation for depth 13, residue 5468. -/
theorem bounds_13_5468 : exactInterval 13 5468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5468 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5468) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5468 : oddCount 5468 13 = 6 ∧ acceleratedOrbit 13 5468 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5468 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5468) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5468.1, data_13_5468.2]

/-- Complete interval computation for depth 13, residue 5469. -/
theorem bounds_13_5469 : exactInterval 13 5469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5469 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5469) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5469 : oddCount 5469 13 = 6 ∧ acceleratedOrbit 13 5469 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5469 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5469) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5469.1, data_13_5469.2]

/-- Complete interval computation for depth 13, residue 5470. -/
theorem bounds_13_5470 : exactInterval 13 5470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5470 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5470) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5470 : oddCount 5470 13 = 6 ∧ acceleratedOrbit 13 5470 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5470 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5470) = 3 ^ 6 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5470.1, data_13_5470.2]

/-- Complete interval computation for depth 13, residue 5471. -/
theorem bounds_13_5471 : exactInterval 13 5471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5471 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5471) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5471 : oddCount 5471 13 = 6 ∧ acceleratedOrbit 13 5471 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5471 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5471) = 3 ^ 6 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5471.1, data_13_5471.2]

/-- Complete interval computation for depth 13, residue 5472. -/
theorem bounds_13_5472 : exactInterval 13 5472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5472 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5472) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5472 : oddCount 5472 13 = 5 ∧ acceleratedOrbit 13 5472 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5472 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5472) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5472.1, data_13_5472.2]

end Collatz.Research.StoppingAtlas.Batch0823
