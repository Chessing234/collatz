import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0104

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 558. -/
theorem bounds_11_558 : exactInterval 11 558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_558 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 558) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_558 : oddCount 558 11 = 5 ∧ acceleratedOrbit 11 558 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_558 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 558) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_558.1, data_11_558.2]

/-- Complete interval computation for depth 11, residue 559. -/
theorem bounds_11_559 : exactInterval 11 559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_559 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 559) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_559 : oddCount 559 11 = 8 ∧ acceleratedOrbit 11 559 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_559 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 559) = 3 ^ 8 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_559.1, data_11_559.2]

/-- Complete interval computation for depth 11, residue 560. -/
theorem bounds_11_560 : exactInterval 11 560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_560 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 560) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_560 : oddCount 560 11 = 3 ∧ acceleratedOrbit 11 560 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_560 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 560) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_560.1, data_11_560.2]

/-- Complete interval computation for depth 11, residue 561. -/
theorem bounds_11_561 : exactInterval 11 561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_561 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 561) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_561 : oddCount 561 11 = 6 ∧ acceleratedOrbit 11 561 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_561 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 561) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_561.1, data_11_561.2]

/-- Complete interval computation for depth 11, residue 562. -/
theorem bounds_11_562 : exactInterval 11 562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_562 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 562) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_562 : oddCount 562 11 = 6 ∧ acceleratedOrbit 11 562 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_562 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 562) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_562.1, data_11_562.2]

/-- Complete interval computation for depth 11, residue 563. -/
theorem bounds_11_563 : exactInterval 11 563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_563 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 563) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_563 : oddCount 563 11 = 6 ∧ acceleratedOrbit 11 563 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_563 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 563) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_563.1, data_11_563.2]

/-- Complete interval computation for depth 11, residue 564. -/
theorem bounds_11_564 : exactInterval 11 564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_564 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 564) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_564 : oddCount 564 11 = 3 ∧ acceleratedOrbit 11 564 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_564 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 564) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_564.1, data_11_564.2]

/-- Complete interval computation for depth 11, residue 565. -/
theorem bounds_11_565 : exactInterval 11 565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_565 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 565) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_565 : oddCount 565 11 = 3 ∧ acceleratedOrbit 11 565 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_565 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 565) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_565.1, data_11_565.2]

/-- Complete interval computation for depth 11, residue 566. -/
theorem bounds_11_566 : exactInterval 11 566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_566 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 566) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_566 : oddCount 566 11 = 8 ∧ acceleratedOrbit 11 566 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_566 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 566) = 3 ^ 8 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_566.1, data_11_566.2]

/-- Complete interval computation for depth 11, residue 567. -/
theorem bounds_11_567 : exactInterval 11 567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_567 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 567) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_567 : oddCount 567 11 = 8 ∧ acceleratedOrbit 11 567 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_567 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 567) = 3 ^ 8 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_567.1, data_11_567.2]

/-- Complete interval computation for depth 11, residue 568. -/
theorem bounds_11_568 : exactInterval 11 568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_568 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 568) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_568 : oddCount 568 11 = 6 ∧ acceleratedOrbit 11 568 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_568 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 568) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_568.1, data_11_568.2]

/-- Complete interval computation for depth 11, residue 569. -/
theorem bounds_11_569 : exactInterval 11 569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_569 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 569) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_569 : oddCount 569 11 = 7 ∧ acceleratedOrbit 11 569 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_569 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 569) = 3 ^ 7 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_569.1, data_11_569.2]

/-- Complete interval computation for depth 11, residue 570. -/
theorem bounds_11_570 : exactInterval 11 570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_570 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 570) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_570 : oddCount 570 11 = 6 ∧ acceleratedOrbit 11 570 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_570 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 570) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_570.1, data_11_570.2]

/-- Complete interval computation for depth 11, residue 571. -/
theorem bounds_11_571 : exactInterval 11 571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_571 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 571) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_571 : oddCount 571 11 = 5 ∧ acceleratedOrbit 11 571 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_571 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 571) = 3 ^ 5 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_571.1, data_11_571.2]

/-- Complete interval computation for depth 11, residue 572. -/
theorem bounds_11_572 : exactInterval 11 572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_572 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 572) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_572 : oddCount 572 11 = 6 ∧ acceleratedOrbit 11 572 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_572 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 572) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_572.1, data_11_572.2]

end Collatz.Research.StoppingAtlas.Batch0104
