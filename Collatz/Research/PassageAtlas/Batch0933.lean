import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0933

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30539. -/
theorem bounds_15_30539 : exactInterval 15 30539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30539 : oddCount 30539 15 = 5 ∧ acceleratedOrbit 15 30539 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30539) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30539.1, data_15_30539.2]

/-- Complete interval computation for depth 15, residue 30540. -/
theorem bounds_15_30540 : exactInterval 15 30540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30540 : oddCount 30540 15 = 7 ∧ acceleratedOrbit 15 30540 = 2039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30540) = 3 ^ 7 * m + 2039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30540.1, data_15_30540.2]

/-- Complete interval computation for depth 15, residue 30541. -/
theorem bounds_15_30541 : exactInterval 15 30541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30541 : oddCount 30541 15 = 7 ∧ acceleratedOrbit 15 30541 = 2039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30541) = 3 ^ 7 * m + 2039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30541.1, data_15_30541.2]

/-- Complete interval computation for depth 15, residue 30542. -/
theorem bounds_15_30542 : exactInterval 15 30542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30542 : oddCount 30542 15 = 8 ∧ acceleratedOrbit 15 30542 = 6116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30542) = 3 ^ 8 * m + 6116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30542.1, data_15_30542.2]

/-- Complete interval computation for depth 15, residue 30543. -/
theorem bounds_15_30543 : exactInterval 15 30543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30543 : oddCount 30543 15 = 8 ∧ acceleratedOrbit 15 30543 = 6116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30543) = 3 ^ 8 * m + 6116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30543.1, data_15_30543.2]

/-- Complete interval computation for depth 15, residue 30544. -/
theorem bounds_15_30544 : exactInterval 15 30544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30544 : oddCount 30544 15 = 4 ∧ acceleratedOrbit 15 30544 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30544) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30544.1, data_15_30544.2]

/-- Complete interval computation for depth 15, residue 30545. -/
theorem bounds_15_30545 : exactInterval 15 30545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30545 : oddCount 30545 15 = 7 ∧ acceleratedOrbit 15 30545 = 2039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30545) = 3 ^ 7 * m + 2039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30545.1, data_15_30545.2]

/-- Complete interval computation for depth 15, residue 30546. -/
theorem bounds_15_30546 : exactInterval 15 30546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30546 : oddCount 30546 15 = 10 ∧ acceleratedOrbit 15 30546 = 55052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30546) = 3 ^ 10 * m + 55052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30546.1, data_15_30546.2]

/-- Complete interval computation for depth 15, residue 30547. -/
theorem bounds_15_30547 : exactInterval 15 30547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30547 : oddCount 30547 15 = 10 ∧ acceleratedOrbit 15 30547 = 55052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30547) = 3 ^ 10 * m + 55052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30547.1, data_15_30547.2]

/-- Complete interval computation for depth 15, residue 30548. -/
theorem bounds_15_30548 : exactInterval 15 30548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30548 : oddCount 30548 15 = 4 ∧ acceleratedOrbit 15 30548 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30548) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30548.1, data_15_30548.2]

/-- Complete interval computation for depth 15, residue 30549. -/
theorem bounds_15_30549 : exactInterval 15 30549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30549 : oddCount 30549 15 = 4 ∧ acceleratedOrbit 15 30549 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30549) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30549.1, data_15_30549.2]

/-- Complete interval computation for depth 15, residue 30550. -/
theorem bounds_15_30550 : exactInterval 15 30550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30550 : oddCount 30550 15 = 8 ∧ acceleratedOrbit 15 30550 = 6119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30550) = 3 ^ 8 * m + 6119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30550.1, data_15_30550.2]

/-- Complete interval computation for depth 15, residue 30551. -/
theorem bounds_15_30551 : exactInterval 15 30551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30551 : oddCount 30551 15 = 8 ∧ acceleratedOrbit 15 30551 = 6119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30551) = 3 ^ 8 * m + 6119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30551.1, data_15_30551.2]

/-- Complete interval computation for depth 15, residue 30552. -/
theorem bounds_15_30552 : exactInterval 15 30552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30552 : oddCount 30552 15 = 6 ∧ acceleratedOrbit 15 30552 = 680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30552) = 3 ^ 6 * m + 680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30552.1, data_15_30552.2]

/-- Complete interval computation for depth 15, residue 30553. -/
theorem bounds_15_30553 : exactInterval 15 30553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30553 : oddCount 30553 15 = 6 ∧ acceleratedOrbit 15 30553 = 680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30553) = 3 ^ 6 * m + 680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30553.1, data_15_30553.2]

/-- Complete interval computation for depth 15, residue 30554. -/
theorem bounds_15_30554 : exactInterval 15 30554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30554 : oddCount 30554 15 = 6 ∧ acceleratedOrbit 15 30554 = 680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30554) = 3 ^ 6 * m + 680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30554.1, data_15_30554.2]

/-- Complete interval computation for depth 15, residue 30555. -/
theorem bounds_15_30555 : exactInterval 15 30555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30555 : oddCount 30555 15 = 9 ∧ acceleratedOrbit 15 30555 = 18355 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30555) = 3 ^ 9 * m + 18355 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30555.1, data_15_30555.2]

/-- Complete interval computation for depth 15, residue 30556. -/
theorem bounds_15_30556 : exactInterval 15 30556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30556 : oddCount 30556 15 = 6 ∧ acceleratedOrbit 15 30556 = 680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30556) = 3 ^ 6 * m + 680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30556.1, data_15_30556.2]

/-- Complete interval computation for depth 15, residue 30557. -/
theorem bounds_15_30557 : exactInterval 15 30557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30557 : oddCount 30557 15 = 6 ∧ acceleratedOrbit 15 30557 = 680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30557) = 3 ^ 6 * m + 680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30557.1, data_15_30557.2]

/-- Complete interval computation for depth 15, residue 30558. -/
theorem bounds_15_30558 : exactInterval 15 30558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30558 : oddCount 30558 15 = 6 ∧ acceleratedOrbit 15 30558 = 680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30558) = 3 ^ 6 * m + 680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30558.1, data_15_30558.2]

/-- Complete interval computation for depth 15, residue 30559. -/
theorem bounds_15_30559 : exactInterval 15 30559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30559 : oddCount 30559 15 = 6 ∧ acceleratedOrbit 15 30559 = 680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30559) = 3 ^ 6 * m + 680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30559.1, data_15_30559.2]

/-- Complete interval computation for depth 15, residue 30560. -/
theorem bounds_15_30560 : exactInterval 15 30560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30560 : oddCount 30560 15 = 5 ∧ acceleratedOrbit 15 30560 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30560) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30560.1, data_15_30560.2]

/-- Complete interval computation for depth 15, residue 30561. -/
theorem bounds_15_30561 : exactInterval 15 30561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30561 : oddCount 30561 15 = 10 ∧ acceleratedOrbit 15 30561 = 55079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30561) = 3 ^ 10 * m + 55079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30561.1, data_15_30561.2]

/-- Complete interval computation for depth 15, residue 30562. -/
theorem bounds_15_30562 : exactInterval 15 30562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30562 : oddCount 30562 15 = 5 ∧ acceleratedOrbit 15 30562 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30562) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30562.1, data_15_30562.2]

/-- Complete interval computation for depth 15, residue 30563. -/
theorem bounds_15_30563 : exactInterval 15 30563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30563 : oddCount 30563 15 = 5 ∧ acceleratedOrbit 15 30563 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30563) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30563.1, data_15_30563.2]

/-- Complete interval computation for depth 15, residue 30564. -/
theorem bounds_15_30564 : exactInterval 15 30564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30564 : oddCount 30564 15 = 5 ∧ acceleratedOrbit 15 30564 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30564) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30564.1, data_15_30564.2]

/-- Complete interval computation for depth 15, residue 30565. -/
theorem bounds_15_30565 : exactInterval 15 30565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30565 : oddCount 30565 15 = 5 ∧ acceleratedOrbit 15 30565 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30565) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30565.1, data_15_30565.2]

/-- Complete interval computation for depth 15, residue 30566. -/
theorem bounds_15_30566 : exactInterval 15 30566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30566 : oddCount 30566 15 = 5 ∧ acceleratedOrbit 15 30566 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30566) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30566.1, data_15_30566.2]

/-- Complete interval computation for depth 15, residue 30567. -/
theorem bounds_15_30567 : exactInterval 15 30567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30567 : oddCount 30567 15 = 10 ∧ acceleratedOrbit 15 30567 = 55085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30567) = 3 ^ 10 * m + 55085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30567.1, data_15_30567.2]

/-- Complete interval computation for depth 15, residue 30568. -/
theorem bounds_15_30568 : exactInterval 15 30568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30568 : oddCount 30568 15 = 5 ∧ acceleratedOrbit 15 30568 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30568) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30568.1, data_15_30568.2]

/-- Complete interval computation for depth 15, residue 30569. -/
theorem bounds_15_30569 : exactInterval 15 30569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30569 : oddCount 30569 15 = 8 ∧ acceleratedOrbit 15 30569 = 6122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30569) = 3 ^ 8 * m + 6122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30569.1, data_15_30569.2]

/-- Complete interval computation for depth 15, residue 30570. -/
theorem bounds_15_30570 : exactInterval 15 30570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30570 : oddCount 30570 15 = 5 ∧ acceleratedOrbit 15 30570 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30570) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30570.1, data_15_30570.2]

/-- Complete interval computation for depth 15, residue 30571. -/
theorem bounds_15_30571 : exactInterval 15 30571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30571 : oddCount 30571 15 = 8 ∧ acceleratedOrbit 15 30571 = 6122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30571) = 3 ^ 8 * m + 6122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30571.1, data_15_30571.2]

end Collatz.Research.PassageAtlas.Batch0933
