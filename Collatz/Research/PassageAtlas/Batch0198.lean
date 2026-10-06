import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0198

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6455. -/
theorem bounds_15_6455 : exactInterval 15 6455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6455 : oddCount 6455 15 = 11 ∧ acceleratedOrbit 15 6455 = 34910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6455) = 3 ^ 11 * m + 34910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6455.1, data_15_6455.2]

/-- Complete interval computation for depth 15, residue 6456. -/
theorem bounds_15_6456 : exactInterval 15 6456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6456 : oddCount 6456 15 = 9 ∧ acceleratedOrbit 15 6456 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6456) = 3 ^ 9 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6456.1, data_15_6456.2]

/-- Complete interval computation for depth 15, residue 6457. -/
theorem bounds_15_6457 : exactInterval 15 6457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6457 : oddCount 6457 15 = 9 ∧ acceleratedOrbit 15 6457 = 3881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6457) = 3 ^ 9 * m + 3881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6457.1, data_15_6457.2]

/-- Complete interval computation for depth 15, residue 6458. -/
theorem bounds_15_6458 : exactInterval 15 6458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6458 : oddCount 6458 15 = 9 ∧ acceleratedOrbit 15 6458 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6458) = 3 ^ 9 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6458.1, data_15_6458.2]

/-- Complete interval computation for depth 15, residue 6459. -/
theorem bounds_15_6459 : exactInterval 15 6459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6459 : oddCount 6459 15 = 9 ∧ acceleratedOrbit 15 6459 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6459) = 3 ^ 9 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6459.1, data_15_6459.2]

/-- Complete interval computation for depth 15, residue 6460. -/
theorem bounds_15_6460 : exactInterval 15 6460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6460 : oddCount 6460 15 = 9 ∧ acceleratedOrbit 15 6460 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6460) = 3 ^ 9 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6460.1, data_15_6460.2]

/-- Complete interval computation for depth 15, residue 6461. -/
theorem bounds_15_6461 : exactInterval 15 6461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6461 : oddCount 6461 15 = 9 ∧ acceleratedOrbit 15 6461 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6461) = 3 ^ 9 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6461.1, data_15_6461.2]

/-- Complete interval computation for depth 15, residue 6462. -/
theorem bounds_15_6462 : exactInterval 15 6462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6462 : oddCount 6462 15 = 12 ∧ acceleratedOrbit 15 6462 = 104840 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6462) = 3 ^ 12 * m + 104840 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6462.1, data_15_6462.2]

/-- Complete interval computation for depth 15, residue 6463. -/
theorem bounds_15_6463 : exactInterval 15 6463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6463 : oddCount 6463 15 = 12 ∧ acceleratedOrbit 15 6463 = 104840 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6463) = 3 ^ 12 * m + 104840 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6463.1, data_15_6463.2]

/-- Complete interval computation for depth 15, residue 6464. -/
theorem bounds_15_6464 : exactInterval 15 6464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6464 : oddCount 6464 15 = 4 ∧ acceleratedOrbit 15 6464 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6464) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6464.1, data_15_6464.2]

/-- Complete interval computation for depth 15, residue 6465. -/
theorem bounds_15_6465 : exactInterval 15 6465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6465 : oddCount 6465 15 = 4 ∧ acceleratedOrbit 15 6465 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6465) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6465.1, data_15_6465.2]

/-- Complete interval computation for depth 15, residue 6466. -/
theorem bounds_15_6466 : exactInterval 15 6466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6466 : oddCount 6466 15 = 11 ∧ acceleratedOrbit 15 6466 = 34991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6466) = 3 ^ 11 * m + 34991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6466.1, data_15_6466.2]

/-- Complete interval computation for depth 15, residue 6467. -/
theorem bounds_15_6467 : exactInterval 15 6467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6467 : oddCount 6467 15 = 11 ∧ acceleratedOrbit 15 6467 = 34991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6467) = 3 ^ 11 * m + 34991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6467.1, data_15_6467.2]

/-- Complete interval computation for depth 15, residue 6468. -/
theorem bounds_15_6468 : exactInterval 15 6468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6468 : oddCount 6468 15 = 7 ∧ acceleratedOrbit 15 6468 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6468) = 3 ^ 7 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6468.1, data_15_6468.2]

/-- Complete interval computation for depth 15, residue 6469. -/
theorem bounds_15_6469 : exactInterval 15 6469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6469 : oddCount 6469 15 = 7 ∧ acceleratedOrbit 15 6469 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6469) = 3 ^ 7 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6469.1, data_15_6469.2]

/-- Complete interval computation for depth 15, residue 6470. -/
theorem bounds_15_6470 : exactInterval 15 6470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6470 : oddCount 6470 15 = 7 ∧ acceleratedOrbit 15 6470 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6470) = 3 ^ 7 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6470.1, data_15_6470.2]

/-- Complete interval computation for depth 15, residue 6471. -/
theorem bounds_15_6471 : exactInterval 15 6471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6471 : oddCount 6471 15 = 13 ∧ acceleratedOrbit 15 6471 = 314927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6471) = 3 ^ 13 * m + 314927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6471.1, data_15_6471.2]

/-- Complete interval computation for depth 15, residue 6472. -/
theorem bounds_15_6472 : exactInterval 15 6472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6472 : oddCount 6472 15 = 7 ∧ acceleratedOrbit 15 6472 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6472) = 3 ^ 7 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6472.1, data_15_6472.2]

/-- Complete interval computation for depth 15, residue 6473. -/
theorem bounds_15_6473 : exactInterval 15 6473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6473 : oddCount 6473 15 = 8 ∧ acceleratedOrbit 15 6473 = 1297 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6473) = 3 ^ 8 * m + 1297 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6473.1, data_15_6473.2]

/-- Complete interval computation for depth 15, residue 6474. -/
theorem bounds_15_6474 : exactInterval 15 6474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6474 : oddCount 6474 15 = 7 ∧ acceleratedOrbit 15 6474 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6474) = 3 ^ 7 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6474.1, data_15_6474.2]

/-- Complete interval computation for depth 15, residue 6475. -/
theorem bounds_15_6475 : exactInterval 15 6475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6475 : oddCount 6475 15 = 7 ∧ acceleratedOrbit 15 6475 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6475) = 3 ^ 7 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6475.1, data_15_6475.2]

/-- Complete interval computation for depth 15, residue 6476. -/
theorem bounds_15_6476 : exactInterval 15 6476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6476 : oddCount 6476 15 = 7 ∧ acceleratedOrbit 15 6476 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6476) = 3 ^ 7 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6476.1, data_15_6476.2]

/-- Complete interval computation for depth 15, residue 6477. -/
theorem bounds_15_6477 : exactInterval 15 6477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6477 : oddCount 6477 15 = 7 ∧ acceleratedOrbit 15 6477 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6477) = 3 ^ 7 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6477.1, data_15_6477.2]

/-- Complete interval computation for depth 15, residue 6478. -/
theorem bounds_15_6478 : exactInterval 15 6478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6478 : oddCount 6478 15 = 9 ∧ acceleratedOrbit 15 6478 = 3893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6478) = 3 ^ 9 * m + 3893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6478.1, data_15_6478.2]

/-- Complete interval computation for depth 15, residue 6479. -/
theorem bounds_15_6479 : exactInterval 15 6479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6479 : oddCount 6479 15 = 9 ∧ acceleratedOrbit 15 6479 = 3893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6479) = 3 ^ 9 * m + 3893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6479.1, data_15_6479.2]

/-- Complete interval computation for depth 15, residue 6480. -/
theorem bounds_15_6480 : exactInterval 15 6480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6480 : oddCount 6480 15 = 4 ∧ acceleratedOrbit 15 6480 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6480) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6480.1, data_15_6480.2]

/-- Complete interval computation for depth 15, residue 6481. -/
theorem bounds_15_6481 : exactInterval 15 6481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6481 : oddCount 6481 15 = 9 ∧ acceleratedOrbit 15 6481 = 3896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6481) = 3 ^ 9 * m + 3896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6481.1, data_15_6481.2]

/-- Complete interval computation for depth 15, residue 6482. -/
theorem bounds_15_6482 : exactInterval 15 6482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6482 : oddCount 6482 15 = 9 ∧ acceleratedOrbit 15 6482 = 3896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6482) = 3 ^ 9 * m + 3896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6482.1, data_15_6482.2]

/-- Complete interval computation for depth 15, residue 6483. -/
theorem bounds_15_6483 : exactInterval 15 6483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6483 : oddCount 6483 15 = 9 ∧ acceleratedOrbit 15 6483 = 3896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6483) = 3 ^ 9 * m + 3896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6483.1, data_15_6483.2]

/-- Complete interval computation for depth 15, residue 6484. -/
theorem bounds_15_6484 : exactInterval 15 6484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6484 : oddCount 6484 15 = 4 ∧ acceleratedOrbit 15 6484 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6484) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6484.1, data_15_6484.2]

/-- Complete interval computation for depth 15, residue 6485. -/
theorem bounds_15_6485 : exactInterval 15 6485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6485 : oddCount 6485 15 = 4 ∧ acceleratedOrbit 15 6485 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6485) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6485.1, data_15_6485.2]

/-- Complete interval computation for depth 15, residue 6486. -/
theorem bounds_15_6486 : exactInterval 15 6486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6486 : oddCount 6486 15 = 7 ∧ acceleratedOrbit 15 6486 = 434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6486) = 3 ^ 7 * m + 434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6486.1, data_15_6486.2]

/-- Complete interval computation for depth 15, residue 6487. -/
theorem bounds_15_6487 : exactInterval 15 6487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6487 : oddCount 6487 15 = 7 ∧ acceleratedOrbit 15 6487 = 434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6487) = 3 ^ 7 * m + 434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6487.1, data_15_6487.2]

end Collatz.Research.PassageAtlas.Batch0198
