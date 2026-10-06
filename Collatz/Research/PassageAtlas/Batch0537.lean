import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0537

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17563. -/
theorem bounds_15_17563 : exactInterval 15 17563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17563 : oddCount 17563 15 = 11 ∧ acceleratedOrbit 15 17563 = 94958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17563) = 3 ^ 11 * m + 94958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17563.1, data_15_17563.2]

/-- Complete interval computation for depth 15, residue 17564. -/
theorem bounds_15_17564 : exactInterval 15 17564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17564 : oddCount 17564 15 = 9 ∧ acceleratedOrbit 15 17564 = 10556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17564) = 3 ^ 9 * m + 10556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17564.1, data_15_17564.2]

/-- Complete interval computation for depth 15, residue 17565. -/
theorem bounds_15_17565 : exactInterval 15 17565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17565 : oddCount 17565 15 = 9 ∧ acceleratedOrbit 15 17565 = 10556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17565) = 3 ^ 9 * m + 10556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17565.1, data_15_17565.2]

/-- Complete interval computation for depth 15, residue 17566. -/
theorem bounds_15_17566 : exactInterval 15 17566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17566 : oddCount 17566 15 = 9 ∧ acceleratedOrbit 15 17566 = 10556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17566) = 3 ^ 9 * m + 10556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17566.1, data_15_17566.2]

/-- Complete interval computation for depth 15, residue 17567. -/
theorem bounds_15_17567 : exactInterval 15 17567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17567 : oddCount 17567 15 = 11 ∧ acceleratedOrbit 15 17567 = 94976 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17567) = 3 ^ 11 * m + 94976 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17567.1, data_15_17567.2]

/-- Complete interval computation for depth 15, residue 17568. -/
theorem bounds_15_17568 : exactInterval 15 17568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17568 : oddCount 17568 15 = 6 ∧ acceleratedOrbit 15 17568 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17568) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17568.1, data_15_17568.2]

/-- Complete interval computation for depth 15, residue 17569. -/
theorem bounds_15_17569 : exactInterval 15 17569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17569 : oddCount 17569 15 = 10 ∧ acceleratedOrbit 15 17569 = 31666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17569) = 3 ^ 10 * m + 31666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17569.1, data_15_17569.2]

/-- Complete interval computation for depth 15, residue 17570. -/
theorem bounds_15_17570 : exactInterval 15 17570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17570 : oddCount 17570 15 = 8 ∧ acceleratedOrbit 15 17570 = 3520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17570) = 3 ^ 8 * m + 3520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17570.1, data_15_17570.2]

/-- Complete interval computation for depth 15, residue 17571. -/
theorem bounds_15_17571 : exactInterval 15 17571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17571 : oddCount 17571 15 = 8 ∧ acceleratedOrbit 15 17571 = 3520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17571) = 3 ^ 8 * m + 3520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17571.1, data_15_17571.2]

/-- Complete interval computation for depth 15, residue 17572. -/
theorem bounds_15_17572 : exactInterval 15 17572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17572 : oddCount 17572 15 = 8 ∧ acceleratedOrbit 15 17572 = 3520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17572) = 3 ^ 8 * m + 3520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17572.1, data_15_17572.2]

/-- Complete interval computation for depth 15, residue 17573. -/
theorem bounds_15_17573 : exactInterval 15 17573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17573 : oddCount 17573 15 = 8 ∧ acceleratedOrbit 15 17573 = 3520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17573) = 3 ^ 8 * m + 3520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17573.1, data_15_17573.2]

/-- Complete interval computation for depth 15, residue 17574. -/
theorem bounds_15_17574 : exactInterval 15 17574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17574 : oddCount 17574 15 = 8 ∧ acceleratedOrbit 15 17574 = 3520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17574) = 3 ^ 8 * m + 3520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17574.1, data_15_17574.2]

/-- Complete interval computation for depth 15, residue 17575. -/
theorem bounds_15_17575 : exactInterval 15 17575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17575 : oddCount 17575 15 = 9 ∧ acceleratedOrbit 15 17575 = 10558 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17575) = 3 ^ 9 * m + 10558 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17575.1, data_15_17575.2]

/-- Complete interval computation for depth 15, residue 17576. -/
theorem bounds_15_17576 : exactInterval 15 17576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17576 : oddCount 17576 15 = 6 ∧ acceleratedOrbit 15 17576 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17576) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17576.1, data_15_17576.2]

/-- Complete interval computation for depth 15, residue 17577. -/
theorem bounds_15_17577 : exactInterval 15 17577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17577 : oddCount 17577 15 = 11 ∧ acceleratedOrbit 15 17577 = 95033 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17577) = 3 ^ 11 * m + 95033 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17577.1, data_15_17577.2]

/-- Complete interval computation for depth 15, residue 17578. -/
theorem bounds_15_17578 : exactInterval 15 17578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17578 : oddCount 17578 15 = 6 ∧ acceleratedOrbit 15 17578 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17578) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17578.1, data_15_17578.2]

/-- Complete interval computation for depth 15, residue 17579. -/
theorem bounds_15_17579 : exactInterval 15 17579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17579 : oddCount 17579 15 = 7 ∧ acceleratedOrbit 15 17579 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17579) = 3 ^ 7 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17579.1, data_15_17579.2]

/-- Complete interval computation for depth 15, residue 17580. -/
theorem bounds_15_17580 : exactInterval 15 17580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17580 : oddCount 17580 15 = 8 ∧ acceleratedOrbit 15 17580 = 3523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17580) = 3 ^ 8 * m + 3523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17580.1, data_15_17580.2]

/-- Complete interval computation for depth 15, residue 17581. -/
theorem bounds_15_17581 : exactInterval 15 17581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17581 : oddCount 17581 15 = 8 ∧ acceleratedOrbit 15 17581 = 3523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17581) = 3 ^ 8 * m + 3523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17581.1, data_15_17581.2]

/-- Complete interval computation for depth 15, residue 17582. -/
theorem bounds_15_17582 : exactInterval 15 17582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17582 : oddCount 17582 15 = 8 ∧ acceleratedOrbit 15 17582 = 3523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17582) = 3 ^ 8 * m + 3523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17582.1, data_15_17582.2]

/-- Complete interval computation for depth 15, residue 17583. -/
theorem bounds_15_17583 : exactInterval 15 17583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17583 : oddCount 17583 15 = 8 ∧ acceleratedOrbit 15 17583 = 3521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17583) = 3 ^ 8 * m + 3521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17583.1, data_15_17583.2]

/-- Complete interval computation for depth 15, residue 17584. -/
theorem bounds_15_17584 : exactInterval 15 17584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17584 : oddCount 17584 15 = 4 ∧ acceleratedOrbit 15 17584 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17584) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17584.1, data_15_17584.2]

/-- Complete interval computation for depth 15, residue 17585. -/
theorem bounds_15_17585 : exactInterval 15 17585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17585 : oddCount 17585 15 = 9 ∧ acceleratedOrbit 15 17585 = 10570 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17585) = 3 ^ 9 * m + 10570 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17585.1, data_15_17585.2]

/-- Complete interval computation for depth 15, residue 17586. -/
theorem bounds_15_17586 : exactInterval 15 17586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17586 : oddCount 17586 15 = 9 ∧ acceleratedOrbit 15 17586 = 10570 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17586) = 3 ^ 9 * m + 10570 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17586.1, data_15_17586.2]

/-- Complete interval computation for depth 15, residue 17587. -/
theorem bounds_15_17587 : exactInterval 15 17587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17587 : oddCount 17587 15 = 9 ∧ acceleratedOrbit 15 17587 = 10570 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17587) = 3 ^ 9 * m + 10570 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17587.1, data_15_17587.2]

/-- Complete interval computation for depth 15, residue 17588. -/
theorem bounds_15_17588 : exactInterval 15 17588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17588 : oddCount 17588 15 = 4 ∧ acceleratedOrbit 15 17588 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17588) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17588.1, data_15_17588.2]

/-- Complete interval computation for depth 15, residue 17589. -/
theorem bounds_15_17589 : exactInterval 15 17589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17589 : oddCount 17589 15 = 4 ∧ acceleratedOrbit 15 17589 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17589) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17589.1, data_15_17589.2]

/-- Complete interval computation for depth 15, residue 17590. -/
theorem bounds_15_17590 : exactInterval 15 17590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17590 : oddCount 17590 15 = 9 ∧ acceleratedOrbit 15 17590 = 10568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17590) = 3 ^ 9 * m + 10568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17590.1, data_15_17590.2]

/-- Complete interval computation for depth 15, residue 17591. -/
theorem bounds_15_17591 : exactInterval 15 17591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17591 : oddCount 17591 15 = 9 ∧ acceleratedOrbit 15 17591 = 10568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17591) = 3 ^ 9 * m + 10568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17591.1, data_15_17591.2]

/-- Complete interval computation for depth 15, residue 17592. -/
theorem bounds_15_17592 : exactInterval 15 17592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17592 : oddCount 17592 15 = 4 ∧ acceleratedOrbit 15 17592 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17592) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17592.1, data_15_17592.2]

/-- Complete interval computation for depth 15, residue 17593. -/
theorem bounds_15_17593 : exactInterval 15 17593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17593 : oddCount 17593 15 = 10 ∧ acceleratedOrbit 15 17593 = 31711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17593) = 3 ^ 10 * m + 31711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17593.1, data_15_17593.2]

/-- Complete interval computation for depth 15, residue 17594. -/
theorem bounds_15_17594 : exactInterval 15 17594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17594 : oddCount 17594 15 = 4 ∧ acceleratedOrbit 15 17594 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17594) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17594.1, data_15_17594.2]

/-- Complete interval computation for depth 15, residue 17595. -/
theorem bounds_15_17595 : exactInterval 15 17595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17595 : oddCount 17595 15 = 11 ∧ acceleratedOrbit 15 17595 = 95134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17595) = 3 ^ 11 * m + 95134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17595.1, data_15_17595.2]

end Collatz.Research.PassageAtlas.Batch0537
