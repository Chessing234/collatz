import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0018

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 557. -/
theorem bounds_15_557 : exactInterval 15 557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_557 : oddCount 557 15 = 7 ∧ acceleratedOrbit 15 557 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 557) = 3 ^ 7 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_557.1, data_15_557.2]

/-- Complete interval computation for depth 15, residue 558. -/
theorem bounds_15_558 : exactInterval 15 558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_558 : oddCount 558 15 = 7 ∧ acceleratedOrbit 15 558 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 558) = 3 ^ 7 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_558.1, data_15_558.2]

/-- Complete interval computation for depth 15, residue 559. -/
theorem bounds_15_559 : exactInterval 15 559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_559 : oddCount 559 15 = 10 ∧ acceleratedOrbit 15 559 = 1010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 559) = 3 ^ 10 * m + 1010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_559.1, data_15_559.2]

/-- Complete interval computation for depth 15, residue 560. -/
theorem bounds_15_560 : exactInterval 15 560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_560 : oddCount 560 15 = 4 ∧ acceleratedOrbit 15 560 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 560) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_560.1, data_15_560.2]

/-- Complete interval computation for depth 15, residue 561. -/
theorem bounds_15_561 : exactInterval 15 561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_561 : oddCount 561 15 = 7 ∧ acceleratedOrbit 15 561 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 561) = 3 ^ 7 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_561.1, data_15_561.2]

/-- Complete interval computation for depth 15, residue 562. -/
theorem bounds_15_562 : exactInterval 15 562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_562 : oddCount 562 15 = 7 ∧ acceleratedOrbit 15 562 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 562) = 3 ^ 7 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_562.1, data_15_562.2]

/-- Complete interval computation for depth 15, residue 563. -/
theorem bounds_15_563 : exactInterval 15 563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_563 : oddCount 563 15 = 7 ∧ acceleratedOrbit 15 563 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 563) = 3 ^ 7 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_563.1, data_15_563.2]

/-- Complete interval computation for depth 15, residue 564. -/
theorem bounds_15_564 : exactInterval 15 564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_564 : oddCount 564 15 = 4 ∧ acceleratedOrbit 15 564 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 564) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_564.1, data_15_564.2]

/-- Complete interval computation for depth 15, residue 565. -/
theorem bounds_15_565 : exactInterval 15 565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_565 : oddCount 565 15 = 4 ∧ acceleratedOrbit 15 565 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 565) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_565.1, data_15_565.2]

/-- Complete interval computation for depth 15, residue 566. -/
theorem bounds_15_566 : exactInterval 15 566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_566 : oddCount 566 15 = 11 ∧ acceleratedOrbit 15 566 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 566) = 3 ^ 11 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_566.1, data_15_566.2]

/-- Complete interval computation for depth 15, residue 567. -/
theorem bounds_15_567 : exactInterval 15 567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_567 : oddCount 567 15 = 11 ∧ acceleratedOrbit 15 567 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 567) = 3 ^ 11 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_567.1, data_15_567.2]

/-- Complete interval computation for depth 15, residue 568. -/
theorem bounds_15_568 : exactInterval 15 568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_568 : oddCount 568 15 = 9 ∧ acceleratedOrbit 15 568 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 568) = 3 ^ 9 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_568.1, data_15_568.2]

/-- Complete interval computation for depth 15, residue 569. -/
theorem bounds_15_569 : exactInterval 15 569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_569 : oddCount 569 15 = 9 ∧ acceleratedOrbit 15 569 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 569) = 3 ^ 9 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_569.1, data_15_569.2]

/-- Complete interval computation for depth 15, residue 570. -/
theorem bounds_15_570 : exactInterval 15 570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_570 : oddCount 570 15 = 9 ∧ acceleratedOrbit 15 570 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 570) = 3 ^ 9 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_570.1, data_15_570.2]

/-- Complete interval computation for depth 15, residue 571. -/
theorem bounds_15_571 : exactInterval 15 571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_571 : oddCount 571 15 = 6 ∧ acceleratedOrbit 15 571 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 571) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_571.1, data_15_571.2]

/-- Complete interval computation for depth 15, residue 572. -/
theorem bounds_15_572 : exactInterval 15 572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_572 : oddCount 572 15 = 9 ∧ acceleratedOrbit 15 572 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 572) = 3 ^ 9 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_572.1, data_15_572.2]

/-- Complete interval computation for depth 15, residue 573. -/
theorem bounds_15_573 : exactInterval 15 573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_573 : oddCount 573 15 = 9 ∧ acceleratedOrbit 15 573 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 573) = 3 ^ 9 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_573.1, data_15_573.2]

/-- Complete interval computation for depth 15, residue 574. -/
theorem bounds_15_574 : exactInterval 15 574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_574 : oddCount 574 15 = 8 ∧ acceleratedOrbit 15 574 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 574) = 3 ^ 8 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_574.1, data_15_574.2]

/-- Complete interval computation for depth 15, residue 575. -/
theorem bounds_15_575 : exactInterval 15 575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_575 : oddCount 575 15 = 8 ∧ acceleratedOrbit 15 575 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 575) = 3 ^ 8 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_575.1, data_15_575.2]

/-- Complete interval computation for depth 15, residue 576. -/
theorem bounds_15_576 : exactInterval 15 576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_576 : oddCount 576 15 = 5 ∧ acceleratedOrbit 15 576 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 576) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_576.1, data_15_576.2]

/-- Complete interval computation for depth 15, residue 577. -/
theorem bounds_15_577 : exactInterval 15 577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_577 : oddCount 577 15 = 7 ∧ acceleratedOrbit 15 577 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 577) = 3 ^ 7 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_577.1, data_15_577.2]

/-- Complete interval computation for depth 15, residue 578. -/
theorem bounds_15_578 : exactInterval 15 578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_578 : oddCount 578 15 = 7 ∧ acceleratedOrbit 15 578 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 578) = 3 ^ 7 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_578.1, data_15_578.2]

/-- Complete interval computation for depth 15, residue 579. -/
theorem bounds_15_579 : exactInterval 15 579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_579 : oddCount 579 15 = 7 ∧ acceleratedOrbit 15 579 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 579) = 3 ^ 7 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_579.1, data_15_579.2]

/-- Complete interval computation for depth 15, residue 580. -/
theorem bounds_15_580 : exactInterval 15 580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_580 : oddCount 580 15 = 8 ∧ acceleratedOrbit 15 580 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 580) = 3 ^ 8 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_580.1, data_15_580.2]

/-- Complete interval computation for depth 15, residue 581. -/
theorem bounds_15_581 : exactInterval 15 581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_581 : oddCount 581 15 = 8 ∧ acceleratedOrbit 15 581 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 581) = 3 ^ 8 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_581.1, data_15_581.2]

/-- Complete interval computation for depth 15, residue 582. -/
theorem bounds_15_582 : exactInterval 15 582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_582 : oddCount 582 15 = 8 ∧ acceleratedOrbit 15 582 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 582) = 3 ^ 8 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_582.1, data_15_582.2]

/-- Complete interval computation for depth 15, residue 583. -/
theorem bounds_15_583 : exactInterval 15 583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_583 : oddCount 583 15 = 6 ∧ acceleratedOrbit 15 583 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 583) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_583.1, data_15_583.2]

/-- Complete interval computation for depth 15, residue 584. -/
theorem bounds_15_584 : exactInterval 15 584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_584 : oddCount 584 15 = 8 ∧ acceleratedOrbit 15 584 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 584) = 3 ^ 8 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_584.1, data_15_584.2]

/-- Complete interval computation for depth 15, residue 585. -/
theorem bounds_15_585 : exactInterval 15 585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_585 : oddCount 585 15 = 8 ∧ acceleratedOrbit 15 585 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 585) = 3 ^ 8 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_585.1, data_15_585.2]

/-- Complete interval computation for depth 15, residue 586. -/
theorem bounds_15_586 : exactInterval 15 586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_586 : oddCount 586 15 = 8 ∧ acceleratedOrbit 15 586 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 586) = 3 ^ 8 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_586.1, data_15_586.2]

/-- Complete interval computation for depth 15, residue 587. -/
theorem bounds_15_587 : exactInterval 15 587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_587 : oddCount 587 15 = 8 ∧ acceleratedOrbit 15 587 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 587) = 3 ^ 8 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_587.1, data_15_587.2]

/-- Complete interval computation for depth 15, residue 588. -/
theorem bounds_15_588 : exactInterval 15 588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_588 : oddCount 588 15 = 8 ∧ acceleratedOrbit 15 588 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 588) = 3 ^ 8 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_588.1, data_15_588.2]

end Collatz.Research.PassageAtlas.Batch0018
