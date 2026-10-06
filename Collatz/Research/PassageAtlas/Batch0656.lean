import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0656

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21463. -/
theorem bounds_15_21463 : exactInterval 15 21463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21463 : oddCount 21463 15 = 8 ∧ acceleratedOrbit 15 21463 = 4298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21463) = 3 ^ 8 * m + 4298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21463.1, data_15_21463.2]

/-- Complete interval computation for depth 15, residue 21464. -/
theorem bounds_15_21464 : exactInterval 15 21464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21464 : oddCount 21464 15 = 6 ∧ acceleratedOrbit 15 21464 = 478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21464) = 3 ^ 6 * m + 478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21464.1, data_15_21464.2]

/-- Complete interval computation for depth 15, residue 21465. -/
theorem bounds_15_21465 : exactInterval 15 21465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21465 : oddCount 21465 15 = 6 ∧ acceleratedOrbit 15 21465 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21465) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21465.1, data_15_21465.2]

/-- Complete interval computation for depth 15, residue 21466. -/
theorem bounds_15_21466 : exactInterval 15 21466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21466 : oddCount 21466 15 = 6 ∧ acceleratedOrbit 15 21466 = 478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21466) = 3 ^ 6 * m + 478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21466.1, data_15_21466.2]

/-- Complete interval computation for depth 15, residue 21467. -/
theorem bounds_15_21467 : exactInterval 15 21467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21467 : oddCount 21467 15 = 7 ∧ acceleratedOrbit 15 21467 = 1433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21467) = 3 ^ 7 * m + 1433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21467.1, data_15_21467.2]

/-- Complete interval computation for depth 15, residue 21468. -/
theorem bounds_15_21468 : exactInterval 15 21468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21468 : oddCount 21468 15 = 6 ∧ acceleratedOrbit 15 21468 = 478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21468) = 3 ^ 6 * m + 478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21468.1, data_15_21468.2]

/-- Complete interval computation for depth 15, residue 21469. -/
theorem bounds_15_21469 : exactInterval 15 21469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21469 : oddCount 21469 15 = 6 ∧ acceleratedOrbit 15 21469 = 478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21469) = 3 ^ 6 * m + 478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21469.1, data_15_21469.2]

/-- Complete interval computation for depth 15, residue 21470. -/
theorem bounds_15_21470 : exactInterval 15 21470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21470 : oddCount 21470 15 = 9 ∧ acceleratedOrbit 15 21470 = 12898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21470) = 3 ^ 9 * m + 12898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21470.1, data_15_21470.2]

/-- Complete interval computation for depth 15, residue 21471. -/
theorem bounds_15_21471 : exactInterval 15 21471 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21471) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21471 : oddCount 21471 15 = 9 ∧ acceleratedOrbit 15 21471 = 12898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21471) = 3 ^ 9 * m + 12898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21471.1, data_15_21471.2]

/-- Complete interval computation for depth 15, residue 21472. -/
theorem bounds_15_21472 : exactInterval 15 21472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21472 : oddCount 21472 15 = 8 ∧ acceleratedOrbit 15 21472 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21472) = 3 ^ 8 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21472.1, data_15_21472.2]

/-- Complete interval computation for depth 15, residue 21473. -/
theorem bounds_15_21473 : exactInterval 15 21473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21473 : oddCount 21473 15 = 8 ∧ acceleratedOrbit 15 21473 = 4300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21473) = 3 ^ 8 * m + 4300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21473.1, data_15_21473.2]

/-- Complete interval computation for depth 15, residue 21474. -/
theorem bounds_15_21474 : exactInterval 15 21474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21474 : oddCount 21474 15 = 6 ∧ acceleratedOrbit 15 21474 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21474) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21474.1, data_15_21474.2]

/-- Complete interval computation for depth 15, residue 21475. -/
theorem bounds_15_21475 : exactInterval 15 21475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21475 : oddCount 21475 15 = 6 ∧ acceleratedOrbit 15 21475 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21475) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21475.1, data_15_21475.2]

/-- Complete interval computation for depth 15, residue 21476. -/
theorem bounds_15_21476 : exactInterval 15 21476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21476 : oddCount 21476 15 = 6 ∧ acceleratedOrbit 15 21476 = 478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21476) = 3 ^ 6 * m + 478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21476.1, data_15_21476.2]

/-- Complete interval computation for depth 15, residue 21477. -/
theorem bounds_15_21477 : exactInterval 15 21477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21477 : oddCount 21477 15 = 6 ∧ acceleratedOrbit 15 21477 = 478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21477) = 3 ^ 6 * m + 478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21477.1, data_15_21477.2]

/-- Complete interval computation for depth 15, residue 21478. -/
theorem bounds_15_21478 : exactInterval 15 21478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21478 : oddCount 21478 15 = 6 ∧ acceleratedOrbit 15 21478 = 478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21478) = 3 ^ 6 * m + 478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21478.1, data_15_21478.2]

/-- Complete interval computation for depth 15, residue 21479. -/
theorem bounds_15_21479 : exactInterval 15 21479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21479 : oddCount 21479 15 = 9 ∧ acceleratedOrbit 15 21479 = 12905 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21479) = 3 ^ 9 * m + 12905 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21479.1, data_15_21479.2]

/-- Complete interval computation for depth 15, residue 21480. -/
theorem bounds_15_21480 : exactInterval 15 21480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21480 : oddCount 21480 15 = 8 ∧ acceleratedOrbit 15 21480 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21480) = 3 ^ 8 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21480.1, data_15_21480.2]

/-- Complete interval computation for depth 15, residue 21481. -/
theorem bounds_15_21481 : exactInterval 15 21481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21481 : oddCount 21481 15 = 10 ∧ acceleratedOrbit 15 21481 = 38713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21481) = 3 ^ 10 * m + 38713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21481.1, data_15_21481.2]

/-- Complete interval computation for depth 15, residue 21482. -/
theorem bounds_15_21482 : exactInterval 15 21482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21482 : oddCount 21482 15 = 8 ∧ acceleratedOrbit 15 21482 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21482) = 3 ^ 8 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21482.1, data_15_21482.2]

/-- Complete interval computation for depth 15, residue 21483. -/
theorem bounds_15_21483 : exactInterval 15 21483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21483 : oddCount 21483 15 = 11 ∧ acceleratedOrbit 15 21483 = 116153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21483) = 3 ^ 11 * m + 116153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21483.1, data_15_21483.2]

/-- Complete interval computation for depth 15, residue 21484. -/
theorem bounds_15_21484 : exactInterval 15 21484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21484 : oddCount 21484 15 = 8 ∧ acceleratedOrbit 15 21484 = 4303 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21484) = 3 ^ 8 * m + 4303 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21484.1, data_15_21484.2]

/-- Complete interval computation for depth 15, residue 21485. -/
theorem bounds_15_21485 : exactInterval 15 21485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21485 : oddCount 21485 15 = 8 ∧ acceleratedOrbit 15 21485 = 4303 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21485) = 3 ^ 8 * m + 4303 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21485.1, data_15_21485.2]

/-- Complete interval computation for depth 15, residue 21486. -/
theorem bounds_15_21486 : exactInterval 15 21486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21486 : oddCount 21486 15 = 8 ∧ acceleratedOrbit 15 21486 = 4303 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21486) = 3 ^ 8 * m + 4303 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21486.1, data_15_21486.2]

/-- Complete interval computation for depth 15, residue 21487. -/
theorem bounds_15_21487 : exactInterval 15 21487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21487 : oddCount 21487 15 = 9 ∧ acceleratedOrbit 15 21487 = 12908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21487) = 3 ^ 9 * m + 12908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21487.1, data_15_21487.2]

/-- Complete interval computation for depth 15, residue 21488. -/
theorem bounds_15_21488 : exactInterval 15 21488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21488 : oddCount 21488 15 = 8 ∧ acceleratedOrbit 15 21488 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21488) = 3 ^ 8 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21488.1, data_15_21488.2]

/-- Complete interval computation for depth 15, residue 21489. -/
theorem bounds_15_21489 : exactInterval 15 21489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21489 : oddCount 21489 15 = 8 ∧ acceleratedOrbit 15 21489 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21489) = 3 ^ 8 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21489.1, data_15_21489.2]

/-- Complete interval computation for depth 15, residue 21490. -/
theorem bounds_15_21490 : exactInterval 15 21490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21490 : oddCount 21490 15 = 8 ∧ acceleratedOrbit 15 21490 = 4304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21490) = 3 ^ 8 * m + 4304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21490.1, data_15_21490.2]

/-- Complete interval computation for depth 15, residue 21491. -/
theorem bounds_15_21491 : exactInterval 15 21491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21491 : oddCount 21491 15 = 8 ∧ acceleratedOrbit 15 21491 = 4304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21491) = 3 ^ 8 * m + 4304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21491.1, data_15_21491.2]

/-- Complete interval computation for depth 15, residue 21492. -/
theorem bounds_15_21492 : exactInterval 15 21492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21492 : oddCount 21492 15 = 8 ∧ acceleratedOrbit 15 21492 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21492) = 3 ^ 8 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21492.1, data_15_21492.2]

/-- Complete interval computation for depth 15, residue 21493. -/
theorem bounds_15_21493 : exactInterval 15 21493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21493 : oddCount 21493 15 = 8 ∧ acceleratedOrbit 15 21493 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21493) = 3 ^ 8 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21493.1, data_15_21493.2]

/-- Complete interval computation for depth 15, residue 21494. -/
theorem bounds_15_21494 : exactInterval 15 21494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21494 : oddCount 21494 15 = 7 ∧ acceleratedOrbit 15 21494 = 1435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21494) = 3 ^ 7 * m + 1435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21494.1, data_15_21494.2]

end Collatz.Research.PassageAtlas.Batch0656
