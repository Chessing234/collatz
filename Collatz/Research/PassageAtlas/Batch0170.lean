import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0170

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5537. -/
theorem bounds_15_5537 : exactInterval 15 5537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5537 : oddCount 5537 15 = 7 ∧ acceleratedOrbit 15 5537 = 370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5537) = 3 ^ 7 * m + 370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5537.1, data_15_5537.2]

/-- Complete interval computation for depth 15, residue 5538. -/
theorem bounds_15_5538 : exactInterval 15 5538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5538 : oddCount 5538 15 = 7 ∧ acceleratedOrbit 15 5538 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5538) = 3 ^ 7 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5538.1, data_15_5538.2]

/-- Complete interval computation for depth 15, residue 5539. -/
theorem bounds_15_5539 : exactInterval 15 5539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5539 : oddCount 5539 15 = 7 ∧ acceleratedOrbit 15 5539 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5539) = 3 ^ 7 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5539.1, data_15_5539.2]

/-- Complete interval computation for depth 15, residue 5540. -/
theorem bounds_15_5540 : exactInterval 15 5540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5540 : oddCount 5540 15 = 7 ∧ acceleratedOrbit 15 5540 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5540) = 3 ^ 7 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5540.1, data_15_5540.2]

/-- Complete interval computation for depth 15, residue 5541. -/
theorem bounds_15_5541 : exactInterval 15 5541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5541 : oddCount 5541 15 = 7 ∧ acceleratedOrbit 15 5541 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5541) = 3 ^ 7 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5541.1, data_15_5541.2]

/-- Complete interval computation for depth 15, residue 5542. -/
theorem bounds_15_5542 : exactInterval 15 5542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5542 : oddCount 5542 15 = 7 ∧ acceleratedOrbit 15 5542 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5542) = 3 ^ 7 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5542.1, data_15_5542.2]

/-- Complete interval computation for depth 15, residue 5543. -/
theorem bounds_15_5543 : exactInterval 15 5543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5543 : oddCount 5543 15 = 9 ∧ acceleratedOrbit 15 5543 = 3331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5543) = 3 ^ 9 * m + 3331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5543.1, data_15_5543.2]

/-- Complete interval computation for depth 15, residue 5544. -/
theorem bounds_15_5544 : exactInterval 15 5544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5544 : oddCount 5544 15 = 4 ∧ acceleratedOrbit 15 5544 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5544) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5544.1, data_15_5544.2]

/-- Complete interval computation for depth 15, residue 5545. -/
theorem bounds_15_5545 : exactInterval 15 5545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5545 : oddCount 5545 15 = 9 ∧ acceleratedOrbit 15 5545 = 3332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5545) = 3 ^ 9 * m + 3332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5545.1, data_15_5545.2]

/-- Complete interval computation for depth 15, residue 5546. -/
theorem bounds_15_5546 : exactInterval 15 5546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5546 : oddCount 5546 15 = 4 ∧ acceleratedOrbit 15 5546 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5546) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5546.1, data_15_5546.2]

/-- Complete interval computation for depth 15, residue 5547. -/
theorem bounds_15_5547 : exactInterval 15 5547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5547 : oddCount 5547 15 = 9 ∧ acceleratedOrbit 15 5547 = 3334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5547) = 3 ^ 9 * m + 3334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5547.1, data_15_5547.2]

/-- Complete interval computation for depth 15, residue 5548. -/
theorem bounds_15_5548 : exactInterval 15 5548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5548 : oddCount 5548 15 = 7 ∧ acceleratedOrbit 15 5548 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5548) = 3 ^ 7 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5548.1, data_15_5548.2]

/-- Complete interval computation for depth 15, residue 5549. -/
theorem bounds_15_5549 : exactInterval 15 5549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5549 : oddCount 5549 15 = 7 ∧ acceleratedOrbit 15 5549 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5549) = 3 ^ 7 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5549.1, data_15_5549.2]

/-- Complete interval computation for depth 15, residue 5550. -/
theorem bounds_15_5550 : exactInterval 15 5550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5550 : oddCount 5550 15 = 7 ∧ acceleratedOrbit 15 5550 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5550) = 3 ^ 7 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5550.1, data_15_5550.2]

/-- Complete interval computation for depth 15, residue 5551. -/
theorem bounds_15_5551 : exactInterval 15 5551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5551 : oddCount 5551 15 = 8 ∧ acceleratedOrbit 15 5551 = 1112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5551) = 3 ^ 8 * m + 1112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5551.1, data_15_5551.2]

/-- Complete interval computation for depth 15, residue 5552. -/
theorem bounds_15_5552 : exactInterval 15 5552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5552 : oddCount 5552 15 = 6 ∧ acceleratedOrbit 15 5552 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5552) = 3 ^ 6 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5552.1, data_15_5552.2]

/-- Complete interval computation for depth 15, residue 5553. -/
theorem bounds_15_5553 : exactInterval 15 5553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5553 : oddCount 5553 15 = 6 ∧ acceleratedOrbit 15 5553 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5553) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5553.1, data_15_5553.2]

/-- Complete interval computation for depth 15, residue 5554. -/
theorem bounds_15_5554 : exactInterval 15 5554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5554 : oddCount 5554 15 = 6 ∧ acceleratedOrbit 15 5554 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5554) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5554.1, data_15_5554.2]

/-- Complete interval computation for depth 15, residue 5555. -/
theorem bounds_15_5555 : exactInterval 15 5555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5555 : oddCount 5555 15 = 6 ∧ acceleratedOrbit 15 5555 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5555) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5555.1, data_15_5555.2]

/-- Complete interval computation for depth 15, residue 5556. -/
theorem bounds_15_5556 : exactInterval 15 5556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5556 : oddCount 5556 15 = 6 ∧ acceleratedOrbit 15 5556 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5556) = 3 ^ 6 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5556.1, data_15_5556.2]

/-- Complete interval computation for depth 15, residue 5557. -/
theorem bounds_15_5557 : exactInterval 15 5557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5557 : oddCount 5557 15 = 6 ∧ acceleratedOrbit 15 5557 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5557) = 3 ^ 6 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5557.1, data_15_5557.2]

/-- Complete interval computation for depth 15, residue 5558. -/
theorem bounds_15_5558 : exactInterval 15 5558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5558 : oddCount 5558 15 = 9 ∧ acceleratedOrbit 15 5558 = 3341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5558) = 3 ^ 9 * m + 3341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5558.1, data_15_5558.2]

/-- Complete interval computation for depth 15, residue 5559. -/
theorem bounds_15_5559 : exactInterval 15 5559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5559 : oddCount 5559 15 = 9 ∧ acceleratedOrbit 15 5559 = 3341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5559) = 3 ^ 9 * m + 3341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5559.1, data_15_5559.2]

/-- Complete interval computation for depth 15, residue 5560. -/
theorem bounds_15_5560 : exactInterval 15 5560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5560 : oddCount 5560 15 = 6 ∧ acceleratedOrbit 15 5560 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5560) = 3 ^ 6 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5560.1, data_15_5560.2]

/-- Complete interval computation for depth 15, residue 5561. -/
theorem bounds_15_5561 : exactInterval 15 5561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5561 : oddCount 5561 15 = 6 ∧ acceleratedOrbit 15 5561 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5561) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5561.1, data_15_5561.2]

/-- Complete interval computation for depth 15, residue 5562. -/
theorem bounds_15_5562 : exactInterval 15 5562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5562 : oddCount 5562 15 = 6 ∧ acceleratedOrbit 15 5562 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5562) = 3 ^ 6 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5562.1, data_15_5562.2]

/-- Complete interval computation for depth 15, residue 5563. -/
theorem bounds_15_5563 : exactInterval 15 5563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5563 : oddCount 5563 15 = 8 ∧ acceleratedOrbit 15 5563 = 1115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5563) = 3 ^ 8 * m + 1115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5563.1, data_15_5563.2]

/-- Complete interval computation for depth 15, residue 5564. -/
theorem bounds_15_5564 : exactInterval 15 5564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5564 : oddCount 5564 15 = 9 ∧ acceleratedOrbit 15 5564 = 3347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5564) = 3 ^ 9 * m + 3347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5564.1, data_15_5564.2]

/-- Complete interval computation for depth 15, residue 5565. -/
theorem bounds_15_5565 : exactInterval 15 5565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5565 : oddCount 5565 15 = 9 ∧ acceleratedOrbit 15 5565 = 3347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5565) = 3 ^ 9 * m + 3347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5565.1, data_15_5565.2]

/-- Complete interval computation for depth 15, residue 5566. -/
theorem bounds_15_5566 : exactInterval 15 5566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5566 : oddCount 5566 15 = 9 ∧ acceleratedOrbit 15 5566 = 3347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5566) = 3 ^ 9 * m + 3347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5566.1, data_15_5566.2]

/-- Complete interval computation for depth 15, residue 5567. -/
theorem bounds_15_5567 : exactInterval 15 5567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5567 : oddCount 5567 15 = 12 ∧ acceleratedOrbit 15 5567 = 90305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5567) = 3 ^ 12 * m + 90305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5567.1, data_15_5567.2]

/-- Complete interval computation for depth 15, residue 5568. -/
theorem bounds_15_5568 : exactInterval 15 5568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5568 : oddCount 5568 15 = 4 ∧ acceleratedOrbit 15 5568 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5568) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5568.1, data_15_5568.2]

/-- Complete interval computation for depth 15, residue 5569. -/
theorem bounds_15_5569 : exactInterval 15 5569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5569 : oddCount 5569 15 = 6 ∧ acceleratedOrbit 15 5569 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5569) = 3 ^ 6 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5569.1, data_15_5569.2]

end Collatz.Research.PassageAtlas.Batch0170
