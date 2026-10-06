import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0503

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16449. -/
theorem bounds_15_16449 : exactInterval 15 16449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16449 : oddCount 16449 15 = 8 ∧ acceleratedOrbit 15 16449 = 3296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16449) = 3 ^ 8 * m + 3296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16449.1, data_15_16449.2]

/-- Complete interval computation for depth 15, residue 16450. -/
theorem bounds_15_16450 : exactInterval 15 16450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16450 : oddCount 16450 15 = 8 ∧ acceleratedOrbit 15 16450 = 3296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16450) = 3 ^ 8 * m + 3296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16450.1, data_15_16450.2]

/-- Complete interval computation for depth 15, residue 16451. -/
theorem bounds_15_16451 : exactInterval 15 16451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16451 : oddCount 16451 15 = 8 ∧ acceleratedOrbit 15 16451 = 3296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16451) = 3 ^ 8 * m + 3296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16451.1, data_15_16451.2]

/-- Complete interval computation for depth 15, residue 16452. -/
theorem bounds_15_16452 : exactInterval 15 16452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16452 : oddCount 16452 15 = 6 ∧ acceleratedOrbit 15 16452 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16452) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16452.1, data_15_16452.2]

/-- Complete interval computation for depth 15, residue 16453. -/
theorem bounds_15_16453 : exactInterval 15 16453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16453 : oddCount 16453 15 = 6 ∧ acceleratedOrbit 15 16453 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16453) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16453.1, data_15_16453.2]

/-- Complete interval computation for depth 15, residue 16454. -/
theorem bounds_15_16454 : exactInterval 15 16454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16454 : oddCount 16454 15 = 6 ∧ acceleratedOrbit 15 16454 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16454) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16454.1, data_15_16454.2]

/-- Complete interval computation for depth 15, residue 16455. -/
theorem bounds_15_16455 : exactInterval 15 16455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16455 : oddCount 16455 15 = 10 ∧ acceleratedOrbit 15 16455 = 29656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16455) = 3 ^ 10 * m + 29656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16455.1, data_15_16455.2]

/-- Complete interval computation for depth 15, residue 16456. -/
theorem bounds_15_16456 : exactInterval 15 16456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16456 : oddCount 16456 15 = 7 ∧ acceleratedOrbit 15 16456 = 1100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16456) = 3 ^ 7 * m + 1100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16456.1, data_15_16456.2]

/-- Complete interval computation for depth 15, residue 16457. -/
theorem bounds_15_16457 : exactInterval 15 16457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16457 : oddCount 16457 15 = 9 ∧ acceleratedOrbit 15 16457 = 9887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16457) = 3 ^ 9 * m + 9887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16457.1, data_15_16457.2]

/-- Complete interval computation for depth 15, residue 16458. -/
theorem bounds_15_16458 : exactInterval 15 16458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16458 : oddCount 16458 15 = 7 ∧ acceleratedOrbit 15 16458 = 1100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16458) = 3 ^ 7 * m + 1100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16458.1, data_15_16458.2]

/-- Complete interval computation for depth 15, residue 16459. -/
theorem bounds_15_16459 : exactInterval 15 16459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16459 : oddCount 16459 15 = 6 ∧ acceleratedOrbit 15 16459 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16459) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16459.1, data_15_16459.2]

/-- Complete interval computation for depth 15, residue 16460. -/
theorem bounds_15_16460 : exactInterval 15 16460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16460 : oddCount 16460 15 = 7 ∧ acceleratedOrbit 15 16460 = 1100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16460) = 3 ^ 7 * m + 1100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16460.1, data_15_16460.2]

/-- Complete interval computation for depth 15, residue 16461. -/
theorem bounds_15_16461 : exactInterval 15 16461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16461 : oddCount 16461 15 = 7 ∧ acceleratedOrbit 15 16461 = 1100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16461) = 3 ^ 7 * m + 1100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16461.1, data_15_16461.2]

/-- Complete interval computation for depth 15, residue 16462. -/
theorem bounds_15_16462 : exactInterval 15 16462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16462 : oddCount 16462 15 = 7 ∧ acceleratedOrbit 15 16462 = 1099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16462) = 3 ^ 7 * m + 1099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16462.1, data_15_16462.2]

/-- Complete interval computation for depth 15, residue 16463. -/
theorem bounds_15_16463 : exactInterval 15 16463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16463 : oddCount 16463 15 = 7 ∧ acceleratedOrbit 15 16463 = 1099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16463) = 3 ^ 7 * m + 1099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16463.1, data_15_16463.2]

/-- Complete interval computation for depth 15, residue 16464. -/
theorem bounds_15_16464 : exactInterval 15 16464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16464 : oddCount 16464 15 = 4 ∧ acceleratedOrbit 15 16464 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16464) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16464.1, data_15_16464.2]

/-- Complete interval computation for depth 15, residue 16465. -/
theorem bounds_15_16465 : exactInterval 15 16465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16465 : oddCount 16465 15 = 7 ∧ acceleratedOrbit 15 16465 = 1100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16465) = 3 ^ 7 * m + 1100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16465.1, data_15_16465.2]

/-- Complete interval computation for depth 15, residue 16466. -/
theorem bounds_15_16466 : exactInterval 15 16466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16466 : oddCount 16466 15 = 9 ∧ acceleratedOrbit 15 16466 = 9893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16466) = 3 ^ 9 * m + 9893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16466.1, data_15_16466.2]

/-- Complete interval computation for depth 15, residue 16467. -/
theorem bounds_15_16467 : exactInterval 15 16467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16467 : oddCount 16467 15 = 9 ∧ acceleratedOrbit 15 16467 = 9893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16467) = 3 ^ 9 * m + 9893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16467.1, data_15_16467.2]

/-- Complete interval computation for depth 15, residue 16468. -/
theorem bounds_15_16468 : exactInterval 15 16468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16468 : oddCount 16468 15 = 4 ∧ acceleratedOrbit 15 16468 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16468) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16468.1, data_15_16468.2]

/-- Complete interval computation for depth 15, residue 16469. -/
theorem bounds_15_16469 : exactInterval 15 16469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16469 : oddCount 16469 15 = 4 ∧ acceleratedOrbit 15 16469 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16469) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16469.1, data_15_16469.2]

/-- Complete interval computation for depth 15, residue 16470. -/
theorem bounds_15_16470 : exactInterval 15 16470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16470 : oddCount 16470 15 = 7 ∧ acceleratedOrbit 15 16470 = 1100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16470) = 3 ^ 7 * m + 1100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16470.1, data_15_16470.2]

/-- Complete interval computation for depth 15, residue 16471. -/
theorem bounds_15_16471 : exactInterval 15 16471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16471 : oddCount 16471 15 = 7 ∧ acceleratedOrbit 15 16471 = 1100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16471) = 3 ^ 7 * m + 1100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16471.1, data_15_16471.2]

/-- Complete interval computation for depth 15, residue 16472. -/
theorem bounds_15_16472 : exactInterval 15 16472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16472 : oddCount 16472 15 = 6 ∧ acceleratedOrbit 15 16472 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16472) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16472.1, data_15_16472.2]

/-- Complete interval computation for depth 15, residue 16473. -/
theorem bounds_15_16473 : exactInterval 15 16473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16473 : oddCount 16473 15 = 7 ∧ acceleratedOrbit 15 16473 = 1100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16473) = 3 ^ 7 * m + 1100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16473.1, data_15_16473.2]

/-- Complete interval computation for depth 15, residue 16474. -/
theorem bounds_15_16474 : exactInterval 15 16474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16474 : oddCount 16474 15 = 6 ∧ acceleratedOrbit 15 16474 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16474) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16474.1, data_15_16474.2]

/-- Complete interval computation for depth 15, residue 16475. -/
theorem bounds_15_16475 : exactInterval 15 16475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16475 : oddCount 16475 15 = 11 ∧ acceleratedOrbit 15 16475 = 89075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16475) = 3 ^ 11 * m + 89075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16475.1, data_15_16475.2]

/-- Complete interval computation for depth 15, residue 16476. -/
theorem bounds_15_16476 : exactInterval 15 16476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16476 : oddCount 16476 15 = 6 ∧ acceleratedOrbit 15 16476 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16476) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16476.1, data_15_16476.2]

/-- Complete interval computation for depth 15, residue 16477. -/
theorem bounds_15_16477 : exactInterval 15 16477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16477 : oddCount 16477 15 = 6 ∧ acceleratedOrbit 15 16477 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16477) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16477.1, data_15_16477.2]

/-- Complete interval computation for depth 15, residue 16478. -/
theorem bounds_15_16478 : exactInterval 15 16478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16478 : oddCount 16478 15 = 11 ∧ acceleratedOrbit 15 16478 = 89099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16478) = 3 ^ 11 * m + 89099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16478.1, data_15_16478.2]

/-- Complete interval computation for depth 15, residue 16479. -/
theorem bounds_15_16479 : exactInterval 15 16479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16479 : oddCount 16479 15 = 11 ∧ acceleratedOrbit 15 16479 = 89099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16479) = 3 ^ 11 * m + 89099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16479.1, data_15_16479.2]

/-- Complete interval computation for depth 15, residue 16480. -/
theorem bounds_15_16480 : exactInterval 15 16480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16480 : oddCount 16480 15 = 4 ∧ acceleratedOrbit 15 16480 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16480) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16480.1, data_15_16480.2]

/-- Complete interval computation for depth 15, residue 16481. -/
theorem bounds_15_16481 : exactInterval 15 16481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16481 : oddCount 16481 15 = 9 ∧ acceleratedOrbit 15 16481 = 9902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16481) = 3 ^ 9 * m + 9902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16481.1, data_15_16481.2]

end Collatz.Research.PassageAtlas.Batch0503
