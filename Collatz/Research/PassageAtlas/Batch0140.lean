import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0140

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4554. -/
theorem bounds_15_4554 : exactInterval 15 4554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4554 : oddCount 4554 15 = 8 ∧ acceleratedOrbit 15 4554 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4554) = 3 ^ 8 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4554.1, data_15_4554.2]

/-- Complete interval computation for depth 15, residue 4555. -/
theorem bounds_15_4555 : exactInterval 15 4555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4555 : oddCount 4555 15 = 7 ∧ acceleratedOrbit 15 4555 = 305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4555) = 3 ^ 7 * m + 305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4555.1, data_15_4555.2]

/-- Complete interval computation for depth 15, residue 4556. -/
theorem bounds_15_4556 : exactInterval 15 4556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4556 : oddCount 4556 15 = 8 ∧ acceleratedOrbit 15 4556 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4556) = 3 ^ 8 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4556.1, data_15_4556.2]

/-- Complete interval computation for depth 15, residue 4557. -/
theorem bounds_15_4557 : exactInterval 15 4557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4557 : oddCount 4557 15 = 8 ∧ acceleratedOrbit 15 4557 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4557) = 3 ^ 8 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4557.1, data_15_4557.2]

/-- Complete interval computation for depth 15, residue 4558. -/
theorem bounds_15_4558 : exactInterval 15 4558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4558 : oddCount 4558 15 = 9 ∧ acceleratedOrbit 15 4558 = 2740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4558) = 3 ^ 9 * m + 2740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4558.1, data_15_4558.2]

/-- Complete interval computation for depth 15, residue 4559. -/
theorem bounds_15_4559 : exactInterval 15 4559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4559 : oddCount 4559 15 = 9 ∧ acceleratedOrbit 15 4559 = 2740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4559) = 3 ^ 9 * m + 2740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4559.1, data_15_4559.2]

/-- Complete interval computation for depth 15, residue 4560. -/
theorem bounds_15_4560 : exactInterval 15 4560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4560 : oddCount 4560 15 = 6 ∧ acceleratedOrbit 15 4560 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4560) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4560.1, data_15_4560.2]

/-- Complete interval computation for depth 15, residue 4561. -/
theorem bounds_15_4561 : exactInterval 15 4561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4561 : oddCount 4561 15 = 8 ∧ acceleratedOrbit 15 4561 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4561) = 3 ^ 8 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4561.1, data_15_4561.2]

/-- Complete interval computation for depth 15, residue 4562. -/
theorem bounds_15_4562 : exactInterval 15 4562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4562 : oddCount 4562 15 = 9 ∧ acceleratedOrbit 15 4562 = 2744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4562) = 3 ^ 9 * m + 2744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4562.1, data_15_4562.2]

/-- Complete interval computation for depth 15, residue 4563. -/
theorem bounds_15_4563 : exactInterval 15 4563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4563 : oddCount 4563 15 = 9 ∧ acceleratedOrbit 15 4563 = 2744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4563) = 3 ^ 9 * m + 2744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4563.1, data_15_4563.2]

/-- Complete interval computation for depth 15, residue 4564. -/
theorem bounds_15_4564 : exactInterval 15 4564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4564 : oddCount 4564 15 = 6 ∧ acceleratedOrbit 15 4564 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4564) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4564.1, data_15_4564.2]

/-- Complete interval computation for depth 15, residue 4565. -/
theorem bounds_15_4565 : exactInterval 15 4565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4565 : oddCount 4565 15 = 6 ∧ acceleratedOrbit 15 4565 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4565) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4565.1, data_15_4565.2]

/-- Complete interval computation for depth 15, residue 4566. -/
theorem bounds_15_4566 : exactInterval 15 4566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4566 : oddCount 4566 15 = 7 ∧ acceleratedOrbit 15 4566 = 305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4566) = 3 ^ 7 * m + 305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4566.1, data_15_4566.2]

/-- Complete interval computation for depth 15, residue 4567. -/
theorem bounds_15_4567 : exactInterval 15 4567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4567 : oddCount 4567 15 = 7 ∧ acceleratedOrbit 15 4567 = 305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4567) = 3 ^ 7 * m + 305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4567.1, data_15_4567.2]

/-- Complete interval computation for depth 15, residue 4568. -/
theorem bounds_15_4568 : exactInterval 15 4568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4568 : oddCount 4568 15 = 5 ∧ acceleratedOrbit 15 4568 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4568) = 3 ^ 5 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4568.1, data_15_4568.2]

/-- Complete interval computation for depth 15, residue 4569. -/
theorem bounds_15_4569 : exactInterval 15 4569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4569 : oddCount 4569 15 = 5 ∧ acceleratedOrbit 15 4569 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4569) = 3 ^ 5 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4569.1, data_15_4569.2]

/-- Complete interval computation for depth 15, residue 4570. -/
theorem bounds_15_4570 : exactInterval 15 4570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4570 : oddCount 4570 15 = 5 ∧ acceleratedOrbit 15 4570 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4570) = 3 ^ 5 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4570.1, data_15_4570.2]

/-- Complete interval computation for depth 15, residue 4571. -/
theorem bounds_15_4571 : exactInterval 15 4571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4571 : oddCount 4571 15 = 8 ∧ acceleratedOrbit 15 4571 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4571) = 3 ^ 8 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4571.1, data_15_4571.2]

/-- Complete interval computation for depth 15, residue 4572. -/
theorem bounds_15_4572 : exactInterval 15 4572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4572 : oddCount 4572 15 = 5 ∧ acceleratedOrbit 15 4572 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4572) = 3 ^ 5 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4572.1, data_15_4572.2]

/-- Complete interval computation for depth 15, residue 4573. -/
theorem bounds_15_4573 : exactInterval 15 4573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4573 : oddCount 4573 15 = 5 ∧ acceleratedOrbit 15 4573 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4573) = 3 ^ 5 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4573.1, data_15_4573.2]

/-- Complete interval computation for depth 15, residue 4574. -/
theorem bounds_15_4574 : exactInterval 15 4574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4574 : oddCount 4574 15 = 12 ∧ acceleratedOrbit 15 4574 = 74222 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4574) = 3 ^ 12 * m + 74222 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4574.1, data_15_4574.2]

/-- Complete interval computation for depth 15, residue 4575. -/
theorem bounds_15_4575 : exactInterval 15 4575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4575 : oddCount 4575 15 = 12 ∧ acceleratedOrbit 15 4575 = 74222 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4575) = 3 ^ 12 * m + 74222 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4575.1, data_15_4575.2]

/-- Complete interval computation for depth 15, residue 4576. -/
theorem bounds_15_4576 : exactInterval 15 4576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4576 : oddCount 4576 15 = 6 ∧ acceleratedOrbit 15 4576 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4576) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4576.1, data_15_4576.2]

/-- Complete interval computation for depth 15, residue 4577. -/
theorem bounds_15_4577 : exactInterval 15 4577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4577 : oddCount 4577 15 = 9 ∧ acceleratedOrbit 15 4577 = 2753 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4577) = 3 ^ 9 * m + 2753 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4577.1, data_15_4577.2]

/-- Complete interval computation for depth 15, residue 4578. -/
theorem bounds_15_4578 : exactInterval 15 4578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4578 : oddCount 4578 15 = 6 ∧ acceleratedOrbit 15 4578 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4578) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4578.1, data_15_4578.2]

/-- Complete interval computation for depth 15, residue 4579. -/
theorem bounds_15_4579 : exactInterval 15 4579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4579 : oddCount 4579 15 = 6 ∧ acceleratedOrbit 15 4579 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4579) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4579.1, data_15_4579.2]

/-- Complete interval computation for depth 15, residue 4580. -/
theorem bounds_15_4580 : exactInterval 15 4580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4580 : oddCount 4580 15 = 8 ∧ acceleratedOrbit 15 4580 = 919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4580) = 3 ^ 8 * m + 919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4580.1, data_15_4580.2]

/-- Complete interval computation for depth 15, residue 4581. -/
theorem bounds_15_4581 : exactInterval 15 4581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4581 : oddCount 4581 15 = 8 ∧ acceleratedOrbit 15 4581 = 919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4581) = 3 ^ 8 * m + 919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4581.1, data_15_4581.2]

/-- Complete interval computation for depth 15, residue 4582. -/
theorem bounds_15_4582 : exactInterval 15 4582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4582 : oddCount 4582 15 = 8 ∧ acceleratedOrbit 15 4582 = 919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4582) = 3 ^ 8 * m + 919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4582.1, data_15_4582.2]

/-- Complete interval computation for depth 15, residue 4583. -/
theorem bounds_15_4583 : exactInterval 15 4583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4583 : oddCount 4583 15 = 12 ∧ acceleratedOrbit 15 4583 = 74357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4583) = 3 ^ 12 * m + 74357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4583.1, data_15_4583.2]

/-- Complete interval computation for depth 15, residue 4584. -/
theorem bounds_15_4584 : exactInterval 15 4584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4584 : oddCount 4584 15 = 6 ∧ acceleratedOrbit 15 4584 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4584) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4584.1, data_15_4584.2]

/-- Complete interval computation for depth 15, residue 4585. -/
theorem bounds_15_4585 : exactInterval 15 4585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4585 : oddCount 4585 15 = 9 ∧ acceleratedOrbit 15 4585 = 2756 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4585) = 3 ^ 9 * m + 2756 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4585.1, data_15_4585.2]

/-- Complete interval computation for depth 15, residue 4586. -/
theorem bounds_15_4586 : exactInterval 15 4586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4586 : oddCount 4586 15 = 6 ∧ acceleratedOrbit 15 4586 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4586) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4586.1, data_15_4586.2]

end Collatz.Research.PassageAtlas.Batch0140
