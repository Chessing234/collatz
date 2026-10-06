import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0504

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 558. -/
theorem bounds_13_558 : exactInterval 13 558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_558 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 558) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_558 : oddCount 558 13 = 7 ∧ acceleratedOrbit 13 558 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_558 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 558) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_558.1, data_13_558.2]

/-- Complete interval computation for depth 13, residue 559. -/
theorem bounds_13_559 : exactInterval 13 559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_559 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 559) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_559 : oddCount 559 13 = 10 ∧ acceleratedOrbit 13 559 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_559 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 559) = 3 ^ 10 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_559.1, data_13_559.2]

/-- Complete interval computation for depth 13, residue 560. -/
theorem bounds_13_560 : exactInterval 13 560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_560 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 560) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_560 : oddCount 560 13 = 3 ∧ acceleratedOrbit 13 560 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_560 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 560) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_560.1, data_13_560.2]

/-- Complete interval computation for depth 13, residue 561. -/
theorem bounds_13_561 : exactInterval 13 561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_561 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 561) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_561 : oddCount 561 13 = 7 ∧ acceleratedOrbit 13 561 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_561 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 561) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_561.1, data_13_561.2]

/-- Complete interval computation for depth 13, residue 562. -/
theorem bounds_13_562 : exactInterval 13 562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_562 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 562) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_562 : oddCount 562 13 = 7 ∧ acceleratedOrbit 13 562 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_562 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 562) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_562.1, data_13_562.2]

/-- Complete interval computation for depth 13, residue 563. -/
theorem bounds_13_563 : exactInterval 13 563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_563 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 563) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_563 : oddCount 563 13 = 7 ∧ acceleratedOrbit 13 563 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_563 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 563) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_563.1, data_13_563.2]

/-- Complete interval computation for depth 13, residue 564. -/
theorem bounds_13_564 : exactInterval 13 564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_564 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 564) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_564 : oddCount 564 13 = 3 ∧ acceleratedOrbit 13 564 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_564 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 564) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_564.1, data_13_564.2]

/-- Complete interval computation for depth 13, residue 565. -/
theorem bounds_13_565 : exactInterval 13 565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_565 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 565) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_565 : oddCount 565 13 = 3 ∧ acceleratedOrbit 13 565 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_565 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 565) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_565.1, data_13_565.2]

/-- Complete interval computation for depth 13, residue 566. -/
theorem bounds_13_566 : exactInterval 13 566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_566 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 566) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_566 : oddCount 566 13 = 9 ∧ acceleratedOrbit 13 566 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_566 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 566) = 3 ^ 9 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_566.1, data_13_566.2]

/-- Complete interval computation for depth 13, residue 567. -/
theorem bounds_13_567 : exactInterval 13 567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_567 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 567) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_567 : oddCount 567 13 = 9 ∧ acceleratedOrbit 13 567 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_567 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 567) = 3 ^ 9 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_567.1, data_13_567.2]

/-- Complete interval computation for depth 13, residue 568. -/
theorem bounds_13_568 : exactInterval 13 568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_568 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 568) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_568 : oddCount 568 13 = 7 ∧ acceleratedOrbit 13 568 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_568 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 568) = 3 ^ 7 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_568.1, data_13_568.2]

/-- Complete interval computation for depth 13, residue 569. -/
theorem bounds_13_569 : exactInterval 13 569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_569 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 569) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_569 : oddCount 569 13 = 9 ∧ acceleratedOrbit 13 569 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_569 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 569) = 3 ^ 9 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_569.1, data_13_569.2]

/-- Complete interval computation for depth 13, residue 570. -/
theorem bounds_13_570 : exactInterval 13 570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_570 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 570) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_570 : oddCount 570 13 = 7 ∧ acceleratedOrbit 13 570 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_570 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 570) = 3 ^ 7 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_570.1, data_13_570.2]

/-- Complete interval computation for depth 13, residue 571. -/
theorem bounds_13_571 : exactInterval 13 571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_571 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 571) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_571 : oddCount 571 13 = 5 ∧ acceleratedOrbit 13 571 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_571 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 571) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_571.1, data_13_571.2]

/-- Complete interval computation for depth 13, residue 572. -/
theorem bounds_13_572 : exactInterval 13 572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_572 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 572) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_572 : oddCount 572 13 = 7 ∧ acceleratedOrbit 13 572 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_572 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 572) = 3 ^ 7 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_572.1, data_13_572.2]

end Collatz.Research.StoppingAtlas.Batch0504
