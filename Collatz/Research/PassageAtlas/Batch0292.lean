import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0292

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9535. -/
theorem bounds_15_9535 : exactInterval 15 9535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9535 : oddCount 9535 15 = 10 ∧ acceleratedOrbit 15 9535 = 17185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9535) = 3 ^ 10 * m + 17185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9535.1, data_15_9535.2]

/-- Complete interval computation for depth 15, residue 9536. -/
theorem bounds_15_9536 : exactInterval 15 9536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9536 : oddCount 9536 15 = 4 ∧ acceleratedOrbit 15 9536 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9536) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9536.1, data_15_9536.2]

/-- Complete interval computation for depth 15, residue 9537. -/
theorem bounds_15_9537 : exactInterval 15 9537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9537 : oddCount 9537 15 = 7 ∧ acceleratedOrbit 15 9537 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9537) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9537.1, data_15_9537.2]

/-- Complete interval computation for depth 15, residue 9538. -/
theorem bounds_15_9538 : exactInterval 15 9538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9538 : oddCount 9538 15 = 7 ∧ acceleratedOrbit 15 9538 = 637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9538) = 3 ^ 7 * m + 637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9538.1, data_15_9538.2]

/-- Complete interval computation for depth 15, residue 9539. -/
theorem bounds_15_9539 : exactInterval 15 9539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9539 : oddCount 9539 15 = 7 ∧ acceleratedOrbit 15 9539 = 637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9539) = 3 ^ 7 * m + 637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9539.1, data_15_9539.2]

/-- Complete interval computation for depth 15, residue 9540. -/
theorem bounds_15_9540 : exactInterval 15 9540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9540 : oddCount 9540 15 = 9 ∧ acceleratedOrbit 15 9540 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9540) = 3 ^ 9 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9540.1, data_15_9540.2]

/-- Complete interval computation for depth 15, residue 9541. -/
theorem bounds_15_9541 : exactInterval 15 9541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9541 : oddCount 9541 15 = 9 ∧ acceleratedOrbit 15 9541 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9541) = 3 ^ 9 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9541.1, data_15_9541.2]

/-- Complete interval computation for depth 15, residue 9542. -/
theorem bounds_15_9542 : exactInterval 15 9542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9542 : oddCount 9542 15 = 9 ∧ acceleratedOrbit 15 9542 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9542) = 3 ^ 9 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9542.1, data_15_9542.2]

/-- Complete interval computation for depth 15, residue 9543. -/
theorem bounds_15_9543 : exactInterval 15 9543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9543 : oddCount 9543 15 = 10 ∧ acceleratedOrbit 15 9543 = 17200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9543) = 3 ^ 10 * m + 17200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9543.1, data_15_9543.2]

/-- Complete interval computation for depth 15, residue 9544. -/
theorem bounds_15_9544 : exactInterval 15 9544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9544 : oddCount 9544 15 = 9 ∧ acceleratedOrbit 15 9544 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9544) = 3 ^ 9 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9544.1, data_15_9544.2]

/-- Complete interval computation for depth 15, residue 9545. -/
theorem bounds_15_9545 : exactInterval 15 9545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9545 : oddCount 9545 15 = 8 ∧ acceleratedOrbit 15 9545 = 1912 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9545) = 3 ^ 8 * m + 1912 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9545.1, data_15_9545.2]

/-- Complete interval computation for depth 15, residue 9546. -/
theorem bounds_15_9546 : exactInterval 15 9546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9546 : oddCount 9546 15 = 9 ∧ acceleratedOrbit 15 9546 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9546) = 3 ^ 9 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9546.1, data_15_9546.2]

/-- Complete interval computation for depth 15, residue 9547. -/
theorem bounds_15_9547 : exactInterval 15 9547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9547 : oddCount 9547 15 = 9 ∧ acceleratedOrbit 15 9547 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9547) = 3 ^ 9 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9547.1, data_15_9547.2]

/-- Complete interval computation for depth 15, residue 9548. -/
theorem bounds_15_9548 : exactInterval 15 9548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9548 : oddCount 9548 15 = 9 ∧ acceleratedOrbit 15 9548 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9548) = 3 ^ 9 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9548.1, data_15_9548.2]

/-- Complete interval computation for depth 15, residue 9549. -/
theorem bounds_15_9549 : exactInterval 15 9549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9549 : oddCount 9549 15 = 9 ∧ acceleratedOrbit 15 9549 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9549) = 3 ^ 9 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9549.1, data_15_9549.2]

/-- Complete interval computation for depth 15, residue 9550. -/
theorem bounds_15_9550 : exactInterval 15 9550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9550 : oddCount 9550 15 = 10 ∧ acceleratedOrbit 15 9550 = 17216 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9550) = 3 ^ 10 * m + 17216 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9550.1, data_15_9550.2]

/-- Complete interval computation for depth 15, residue 9551. -/
theorem bounds_15_9551 : exactInterval 15 9551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9551 : oddCount 9551 15 = 10 ∧ acceleratedOrbit 15 9551 = 17216 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9551) = 3 ^ 10 * m + 17216 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9551.1, data_15_9551.2]

/-- Complete interval computation for depth 15, residue 9552. -/
theorem bounds_15_9552 : exactInterval 15 9552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9552 : oddCount 9552 15 = 4 ∧ acceleratedOrbit 15 9552 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9552) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9552.1, data_15_9552.2]

/-- Complete interval computation for depth 15, residue 9553. -/
theorem bounds_15_9553 : exactInterval 15 9553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9553 : oddCount 9553 15 = 11 ∧ acceleratedOrbit 15 9553 = 51668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9553) = 3 ^ 11 * m + 51668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9553.1, data_15_9553.2]

/-- Complete interval computation for depth 15, residue 9554. -/
theorem bounds_15_9554 : exactInterval 15 9554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9554 : oddCount 9554 15 = 11 ∧ acceleratedOrbit 15 9554 = 51668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9554) = 3 ^ 11 * m + 51668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9554.1, data_15_9554.2]

/-- Complete interval computation for depth 15, residue 9555. -/
theorem bounds_15_9555 : exactInterval 15 9555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9555 : oddCount 9555 15 = 11 ∧ acceleratedOrbit 15 9555 = 51668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9555) = 3 ^ 11 * m + 51668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9555.1, data_15_9555.2]

/-- Complete interval computation for depth 15, residue 9556. -/
theorem bounds_15_9556 : exactInterval 15 9556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9556 : oddCount 9556 15 = 4 ∧ acceleratedOrbit 15 9556 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9556) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9556.1, data_15_9556.2]

/-- Complete interval computation for depth 15, residue 9557. -/
theorem bounds_15_9557 : exactInterval 15 9557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9557 : oddCount 9557 15 = 4 ∧ acceleratedOrbit 15 9557 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9557) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9557.1, data_15_9557.2]

/-- Complete interval computation for depth 15, residue 9558. -/
theorem bounds_15_9558 : exactInterval 15 9558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9558 : oddCount 9558 15 = 8 ∧ acceleratedOrbit 15 9558 = 1916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9558) = 3 ^ 8 * m + 1916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9558.1, data_15_9558.2]

/-- Complete interval computation for depth 15, residue 9559. -/
theorem bounds_15_9559 : exactInterval 15 9559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9559 : oddCount 9559 15 = 8 ∧ acceleratedOrbit 15 9559 = 1916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9559) = 3 ^ 8 * m + 1916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9559.1, data_15_9559.2]

/-- Complete interval computation for depth 15, residue 9560. -/
theorem bounds_15_9560 : exactInterval 15 9560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9560 : oddCount 9560 15 = 5 ∧ acceleratedOrbit 15 9560 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9560) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9560.1, data_15_9560.2]

/-- Complete interval computation for depth 15, residue 9561. -/
theorem bounds_15_9561 : exactInterval 15 9561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9561 : oddCount 9561 15 = 9 ∧ acceleratedOrbit 15 9561 = 5750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9561) = 3 ^ 9 * m + 5750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9561.1, data_15_9561.2]

/-- Complete interval computation for depth 15, residue 9562. -/
theorem bounds_15_9562 : exactInterval 15 9562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9562 : oddCount 9562 15 = 5 ∧ acceleratedOrbit 15 9562 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9562) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9562.1, data_15_9562.2]

/-- Complete interval computation for depth 15, residue 9563. -/
theorem bounds_15_9563 : exactInterval 15 9563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9563 : oddCount 9563 15 = 9 ∧ acceleratedOrbit 15 9563 = 5746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9563) = 3 ^ 9 * m + 5746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9563.1, data_15_9563.2]

/-- Complete interval computation for depth 15, residue 9564. -/
theorem bounds_15_9564 : exactInterval 15 9564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9564 : oddCount 9564 15 = 5 ∧ acceleratedOrbit 15 9564 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9564) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9564.1, data_15_9564.2]

/-- Complete interval computation for depth 15, residue 9565. -/
theorem bounds_15_9565 : exactInterval 15 9565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9565 : oddCount 9565 15 = 5 ∧ acceleratedOrbit 15 9565 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9565) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9565.1, data_15_9565.2]

/-- Complete interval computation for depth 15, residue 9566. -/
theorem bounds_15_9566 : exactInterval 15 9566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9566 : oddCount 9566 15 = 9 ∧ acceleratedOrbit 15 9566 = 5750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9566) = 3 ^ 9 * m + 5750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9566.1, data_15_9566.2]

/-- Complete interval computation for depth 15, residue 9567. -/
theorem bounds_15_9567 : exactInterval 15 9567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9567 : oddCount 9567 15 = 9 ∧ acceleratedOrbit 15 9567 = 5750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9567) = 3 ^ 9 * m + 5750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9567.1, data_15_9567.2]

end Collatz.Research.PassageAtlas.Batch0292
