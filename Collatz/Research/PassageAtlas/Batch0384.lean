import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0384

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12550. -/
theorem bounds_15_12550 : exactInterval 15 12550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12550 : oddCount 12550 15 = 6 ∧ acceleratedOrbit 15 12550 = 280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12550) = 3 ^ 6 * m + 280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12550.1, data_15_12550.2]

/-- Complete interval computation for depth 15, residue 12551. -/
theorem bounds_15_12551 : exactInterval 15 12551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12551 : oddCount 12551 15 = 9 ∧ acceleratedOrbit 15 12551 = 7541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12551) = 3 ^ 9 * m + 7541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12551.1, data_15_12551.2]

/-- Complete interval computation for depth 15, residue 12552. -/
theorem bounds_15_12552 : exactInterval 15 12552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12552 : oddCount 12552 15 = 6 ∧ acceleratedOrbit 15 12552 = 280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12552) = 3 ^ 6 * m + 280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12552.1, data_15_12552.2]

/-- Complete interval computation for depth 15, residue 12553. -/
theorem bounds_15_12553 : exactInterval 15 12553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12553 : oddCount 12553 15 = 7 ∧ acceleratedOrbit 15 12553 = 838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12553) = 3 ^ 7 * m + 838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12553.1, data_15_12553.2]

/-- Complete interval computation for depth 15, residue 12554. -/
theorem bounds_15_12554 : exactInterval 15 12554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12554 : oddCount 12554 15 = 6 ∧ acceleratedOrbit 15 12554 = 280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12554) = 3 ^ 6 * m + 280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12554.1, data_15_12554.2]

/-- Complete interval computation for depth 15, residue 12555. -/
theorem bounds_15_12555 : exactInterval 15 12555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12555 : oddCount 12555 15 = 7 ∧ acceleratedOrbit 15 12555 = 839 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12555) = 3 ^ 7 * m + 839 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12555.1, data_15_12555.2]

/-- Complete interval computation for depth 15, residue 12556. -/
theorem bounds_15_12556 : exactInterval 15 12556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12556 : oddCount 12556 15 = 6 ∧ acceleratedOrbit 15 12556 = 280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12556) = 3 ^ 6 * m + 280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12556.1, data_15_12556.2]

/-- Complete interval computation for depth 15, residue 12557. -/
theorem bounds_15_12557 : exactInterval 15 12557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12557 : oddCount 12557 15 = 6 ∧ acceleratedOrbit 15 12557 = 280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12557) = 3 ^ 6 * m + 280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12557.1, data_15_12557.2]

/-- Complete interval computation for depth 15, residue 12558. -/
theorem bounds_15_12558 : exactInterval 15 12558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12558 : oddCount 12558 15 = 7 ∧ acceleratedOrbit 15 12558 = 839 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12558) = 3 ^ 7 * m + 839 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12558.1, data_15_12558.2]

/-- Complete interval computation for depth 15, residue 12559. -/
theorem bounds_15_12559 : exactInterval 15 12559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12559 : oddCount 12559 15 = 7 ∧ acceleratedOrbit 15 12559 = 839 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12559) = 3 ^ 7 * m + 839 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12559.1, data_15_12559.2]

/-- Complete interval computation for depth 15, residue 12560. -/
theorem bounds_15_12560 : exactInterval 15 12560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12560 : oddCount 12560 15 = 5 ∧ acceleratedOrbit 15 12560 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12560) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12560.1, data_15_12560.2]

/-- Complete interval computation for depth 15, residue 12561. -/
theorem bounds_15_12561 : exactInterval 15 12561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12561 : oddCount 12561 15 = 6 ∧ acceleratedOrbit 15 12561 = 280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12561) = 3 ^ 6 * m + 280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12561.1, data_15_12561.2]

/-- Complete interval computation for depth 15, residue 12562. -/
theorem bounds_15_12562 : exactInterval 15 12562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12562 : oddCount 12562 15 = 8 ∧ acceleratedOrbit 15 12562 = 2516 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12562) = 3 ^ 8 * m + 2516 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12562.1, data_15_12562.2]

/-- Complete interval computation for depth 15, residue 12563. -/
theorem bounds_15_12563 : exactInterval 15 12563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12563 : oddCount 12563 15 = 8 ∧ acceleratedOrbit 15 12563 = 2516 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12563) = 3 ^ 8 * m + 2516 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12563.1, data_15_12563.2]

/-- Complete interval computation for depth 15, residue 12564. -/
theorem bounds_15_12564 : exactInterval 15 12564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12564 : oddCount 12564 15 = 5 ∧ acceleratedOrbit 15 12564 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12564) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12564.1, data_15_12564.2]

/-- Complete interval computation for depth 15, residue 12565. -/
theorem bounds_15_12565 : exactInterval 15 12565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12565 : oddCount 12565 15 = 5 ∧ acceleratedOrbit 15 12565 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12565) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12565.1, data_15_12565.2]

/-- Complete interval computation for depth 15, residue 12566. -/
theorem bounds_15_12566 : exactInterval 15 12566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12566 : oddCount 12566 15 = 9 ∧ acceleratedOrbit 15 12566 = 7553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12566) = 3 ^ 9 * m + 7553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12566.1, data_15_12566.2]

/-- Complete interval computation for depth 15, residue 12567. -/
theorem bounds_15_12567 : exactInterval 15 12567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12567 : oddCount 12567 15 = 9 ∧ acceleratedOrbit 15 12567 = 7553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12567) = 3 ^ 9 * m + 7553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12567.1, data_15_12567.2]

/-- Complete interval computation for depth 15, residue 12568. -/
theorem bounds_15_12568 : exactInterval 15 12568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12568 : oddCount 12568 15 = 5 ∧ acceleratedOrbit 15 12568 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12568) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12568.1, data_15_12568.2]

/-- Complete interval computation for depth 15, residue 12569. -/
theorem bounds_15_12569 : exactInterval 15 12569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12569 : oddCount 12569 15 = 9 ∧ acceleratedOrbit 15 12569 = 7553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12569) = 3 ^ 9 * m + 7553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12569.1, data_15_12569.2]

/-- Complete interval computation for depth 15, residue 12570. -/
theorem bounds_15_12570 : exactInterval 15 12570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12570 : oddCount 12570 15 = 5 ∧ acceleratedOrbit 15 12570 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12570) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12570.1, data_15_12570.2]

/-- Complete interval computation for depth 15, residue 12571. -/
theorem bounds_15_12571 : exactInterval 15 12571 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12571) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12571 : oddCount 12571 15 = 9 ∧ acceleratedOrbit 15 12571 = 7552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12571) = 3 ^ 9 * m + 7552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12571.1, data_15_12571.2]

/-- Complete interval computation for depth 15, residue 12572. -/
theorem bounds_15_12572 : exactInterval 15 12572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12572 : oddCount 12572 15 = 8 ∧ acceleratedOrbit 15 12572 = 2519 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12572) = 3 ^ 8 * m + 2519 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12572.1, data_15_12572.2]

/-- Complete interval computation for depth 15, residue 12573. -/
theorem bounds_15_12573 : exactInterval 15 12573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12573 : oddCount 12573 15 = 8 ∧ acceleratedOrbit 15 12573 = 2519 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12573) = 3 ^ 8 * m + 2519 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12573.1, data_15_12573.2]

/-- Complete interval computation for depth 15, residue 12574. -/
theorem bounds_15_12574 : exactInterval 15 12574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12574 : oddCount 12574 15 = 8 ∧ acceleratedOrbit 15 12574 = 2519 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12574) = 3 ^ 8 * m + 2519 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12574.1, data_15_12574.2]

/-- Complete interval computation for depth 15, residue 12575. -/
theorem bounds_15_12575 : exactInterval 15 12575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12575 : oddCount 12575 15 = 9 ∧ acceleratedOrbit 15 12575 = 7555 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12575) = 3 ^ 9 * m + 7555 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12575.1, data_15_12575.2]

/-- Complete interval computation for depth 15, residue 12576. -/
theorem bounds_15_12576 : exactInterval 15 12576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12576 : oddCount 12576 15 = 6 ∧ acceleratedOrbit 15 12576 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12576) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12576.1, data_15_12576.2]

/-- Complete interval computation for depth 15, residue 12577. -/
theorem bounds_15_12577 : exactInterval 15 12577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12577 : oddCount 12577 15 = 6 ∧ acceleratedOrbit 15 12577 = 280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12577) = 3 ^ 6 * m + 280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12577.1, data_15_12577.2]

/-- Complete interval computation for depth 15, residue 12578. -/
theorem bounds_15_12578 : exactInterval 15 12578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12578 : oddCount 12578 15 = 8 ∧ acceleratedOrbit 15 12578 = 2521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12578) = 3 ^ 8 * m + 2521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12578.1, data_15_12578.2]

/-- Complete interval computation for depth 15, residue 12579. -/
theorem bounds_15_12579 : exactInterval 15 12579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12579 : oddCount 12579 15 = 8 ∧ acceleratedOrbit 15 12579 = 2521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12579) = 3 ^ 8 * m + 2521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12579.1, data_15_12579.2]

/-- Complete interval computation for depth 15, residue 12580. -/
theorem bounds_15_12580 : exactInterval 15 12580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12580 : oddCount 12580 15 = 8 ∧ acceleratedOrbit 15 12580 = 2521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12580) = 3 ^ 8 * m + 2521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12580.1, data_15_12580.2]

/-- Complete interval computation for depth 15, residue 12581. -/
theorem bounds_15_12581 : exactInterval 15 12581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12581 : oddCount 12581 15 = 8 ∧ acceleratedOrbit 15 12581 = 2521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12581) = 3 ^ 8 * m + 2521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12581.1, data_15_12581.2]

end Collatz.Research.PassageAtlas.Batch0384
