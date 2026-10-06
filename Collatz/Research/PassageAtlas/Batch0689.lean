import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0689

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22544. -/
theorem bounds_15_22544 : exactInterval 15 22544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22544 : oddCount 22544 15 = 6 ∧ acceleratedOrbit 15 22544 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22544) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22544.1, data_15_22544.2]

/-- Complete interval computation for depth 15, residue 22545. -/
theorem bounds_15_22545 : exactInterval 15 22545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22545 : oddCount 22545 15 = 6 ∧ acceleratedOrbit 15 22545 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22545) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22545.1, data_15_22545.2]

/-- Complete interval computation for depth 15, residue 22546. -/
theorem bounds_15_22546 : exactInterval 15 22546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22546 : oddCount 22546 15 = 9 ∧ acceleratedOrbit 15 22546 = 13547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22546) = 3 ^ 9 * m + 13547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22546.1, data_15_22546.2]

/-- Complete interval computation for depth 15, residue 22547. -/
theorem bounds_15_22547 : exactInterval 15 22547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22547 : oddCount 22547 15 = 9 ∧ acceleratedOrbit 15 22547 = 13547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22547) = 3 ^ 9 * m + 13547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22547.1, data_15_22547.2]

/-- Complete interval computation for depth 15, residue 22548. -/
theorem bounds_15_22548 : exactInterval 15 22548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22548 : oddCount 22548 15 = 6 ∧ acceleratedOrbit 15 22548 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22548) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22548.1, data_15_22548.2]

/-- Complete interval computation for depth 15, residue 22549. -/
theorem bounds_15_22549 : exactInterval 15 22549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22549 : oddCount 22549 15 = 6 ∧ acceleratedOrbit 15 22549 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22549) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22549.1, data_15_22549.2]

/-- Complete interval computation for depth 15, residue 22550. -/
theorem bounds_15_22550 : exactInterval 15 22550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22550 : oddCount 22550 15 = 6 ∧ acceleratedOrbit 15 22550 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22550) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22550.1, data_15_22550.2]

/-- Complete interval computation for depth 15, residue 22551. -/
theorem bounds_15_22551 : exactInterval 15 22551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22551 : oddCount 22551 15 = 6 ∧ acceleratedOrbit 15 22551 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22551) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22551.1, data_15_22551.2]

/-- Complete interval computation for depth 15, residue 22552. -/
theorem bounds_15_22552 : exactInterval 15 22552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22552 : oddCount 22552 15 = 6 ∧ acceleratedOrbit 15 22552 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22552) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22552.1, data_15_22552.2]

/-- Complete interval computation for depth 15, residue 22553. -/
theorem bounds_15_22553 : exactInterval 15 22553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22553 : oddCount 22553 15 = 8 ∧ acceleratedOrbit 15 22553 = 4517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22553) = 3 ^ 8 * m + 4517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22553.1, data_15_22553.2]

/-- Complete interval computation for depth 15, residue 22554. -/
theorem bounds_15_22554 : exactInterval 15 22554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22554 : oddCount 22554 15 = 6 ∧ acceleratedOrbit 15 22554 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22554) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22554.1, data_15_22554.2]

/-- Complete interval computation for depth 15, residue 22555. -/
theorem bounds_15_22555 : exactInterval 15 22555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22555 : oddCount 22555 15 = 10 ∧ acceleratedOrbit 15 22555 = 40648 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22555) = 3 ^ 10 * m + 40648 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22555.1, data_15_22555.2]

/-- Complete interval computation for depth 15, residue 22556. -/
theorem bounds_15_22556 : exactInterval 15 22556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22556 : oddCount 22556 15 = 6 ∧ acceleratedOrbit 15 22556 = 502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22556) = 3 ^ 6 * m + 502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22556.1, data_15_22556.2]

/-- Complete interval computation for depth 15, residue 22557. -/
theorem bounds_15_22557 : exactInterval 15 22557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22557 : oddCount 22557 15 = 6 ∧ acceleratedOrbit 15 22557 = 502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22557) = 3 ^ 6 * m + 502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22557.1, data_15_22557.2]

/-- Complete interval computation for depth 15, residue 22558. -/
theorem bounds_15_22558 : exactInterval 15 22558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22558 : oddCount 22558 15 = 6 ∧ acceleratedOrbit 15 22558 = 502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22558) = 3 ^ 6 * m + 502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22558.1, data_15_22558.2]

/-- Complete interval computation for depth 15, residue 22559. -/
theorem bounds_15_22559 : exactInterval 15 22559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22559 : oddCount 22559 15 = 10 ∧ acceleratedOrbit 15 22559 = 40655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22559) = 3 ^ 10 * m + 40655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22559.1, data_15_22559.2]

/-- Complete interval computation for depth 15, residue 22560. -/
theorem bounds_15_22560 : exactInterval 15 22560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22560 : oddCount 22560 15 = 4 ∧ acceleratedOrbit 15 22560 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22560) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22560.1, data_15_22560.2]

/-- Complete interval computation for depth 15, residue 22561. -/
theorem bounds_15_22561 : exactInterval 15 22561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22561 : oddCount 22561 15 = 6 ∧ acceleratedOrbit 15 22561 = 502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22561) = 3 ^ 6 * m + 502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22561.1, data_15_22561.2]

/-- Complete interval computation for depth 15, residue 22562. -/
theorem bounds_15_22562 : exactInterval 15 22562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22562 : oddCount 22562 15 = 6 ∧ acceleratedOrbit 15 22562 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22562) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22562.1, data_15_22562.2]

/-- Complete interval computation for depth 15, residue 22563. -/
theorem bounds_15_22563 : exactInterval 15 22563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22563 : oddCount 22563 15 = 6 ∧ acceleratedOrbit 15 22563 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22563) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22563.1, data_15_22563.2]

/-- Complete interval computation for depth 15, residue 22564. -/
theorem bounds_15_22564 : exactInterval 15 22564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22564 : oddCount 22564 15 = 7 ∧ acceleratedOrbit 15 22564 = 1507 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22564) = 3 ^ 7 * m + 1507 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22564.1, data_15_22564.2]

/-- Complete interval computation for depth 15, residue 22565. -/
theorem bounds_15_22565 : exactInterval 15 22565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22565 : oddCount 22565 15 = 7 ∧ acceleratedOrbit 15 22565 = 1507 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22565) = 3 ^ 7 * m + 1507 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22565.1, data_15_22565.2]

/-- Complete interval computation for depth 15, residue 22566. -/
theorem bounds_15_22566 : exactInterval 15 22566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22566 : oddCount 22566 15 = 7 ∧ acceleratedOrbit 15 22566 = 1507 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22566) = 3 ^ 7 * m + 1507 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22566.1, data_15_22566.2]

/-- Complete interval computation for depth 15, residue 22567. -/
theorem bounds_15_22567 : exactInterval 15 22567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22567 : oddCount 22567 15 = 8 ∧ acceleratedOrbit 15 22567 = 4519 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22567) = 3 ^ 8 * m + 4519 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22567.1, data_15_22567.2]

/-- Complete interval computation for depth 15, residue 22568. -/
theorem bounds_15_22568 : exactInterval 15 22568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22568 : oddCount 22568 15 = 4 ∧ acceleratedOrbit 15 22568 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22568) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22568.1, data_15_22568.2]

/-- Complete interval computation for depth 15, residue 22569. -/
theorem bounds_15_22569 : exactInterval 15 22569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22569 : oddCount 22569 15 = 9 ∧ acceleratedOrbit 15 22569 = 13558 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22569) = 3 ^ 9 * m + 13558 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22569.1, data_15_22569.2]

/-- Complete interval computation for depth 15, residue 22570. -/
theorem bounds_15_22570 : exactInterval 15 22570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22570 : oddCount 22570 15 = 4 ∧ acceleratedOrbit 15 22570 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22570) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22570.1, data_15_22570.2]

/-- Complete interval computation for depth 15, residue 22571. -/
theorem bounds_15_22571 : exactInterval 15 22571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22571 : oddCount 22571 15 = 7 ∧ acceleratedOrbit 15 22571 = 1507 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22571) = 3 ^ 7 * m + 1507 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22571.1, data_15_22571.2]

/-- Complete interval computation for depth 15, residue 22572. -/
theorem bounds_15_22572 : exactInterval 15 22572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22572 : oddCount 22572 15 = 6 ∧ acceleratedOrbit 15 22572 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22572) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22572.1, data_15_22572.2]

/-- Complete interval computation for depth 15, residue 22573. -/
theorem bounds_15_22573 : exactInterval 15 22573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22573 : oddCount 22573 15 = 6 ∧ acceleratedOrbit 15 22573 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22573) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22573.1, data_15_22573.2]

/-- Complete interval computation for depth 15, residue 22574. -/
theorem bounds_15_22574 : exactInterval 15 22574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22574 : oddCount 22574 15 = 6 ∧ acceleratedOrbit 15 22574 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22574) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22574.1, data_15_22574.2]

/-- Complete interval computation for depth 15, residue 22575. -/
theorem bounds_15_22575 : exactInterval 15 22575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22575 : oddCount 22575 15 = 10 ∧ acceleratedOrbit 15 22575 = 40684 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22575) = 3 ^ 10 * m + 40684 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22575.1, data_15_22575.2]

/-- Complete interval computation for depth 15, residue 22576. -/
theorem bounds_15_22576 : exactInterval 15 22576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22576 : oddCount 22576 15 = 4 ∧ acceleratedOrbit 15 22576 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22576) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22576.1, data_15_22576.2]

end Collatz.Research.PassageAtlas.Batch0689
