import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0539

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17629. -/
theorem bounds_15_17629 : exactInterval 15 17629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17629 : oddCount 17629 15 = 7 ∧ acceleratedOrbit 15 17629 = 1177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17629) = 3 ^ 7 * m + 1177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17629.1, data_15_17629.2]

/-- Complete interval computation for depth 15, residue 17630. -/
theorem bounds_15_17630 : exactInterval 15 17630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17630 : oddCount 17630 15 = 9 ∧ acceleratedOrbit 15 17630 = 10592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17630) = 3 ^ 9 * m + 10592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17630.1, data_15_17630.2]

/-- Complete interval computation for depth 15, residue 17631. -/
theorem bounds_15_17631 : exactInterval 15 17631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17631 : oddCount 17631 15 = 9 ∧ acceleratedOrbit 15 17631 = 10592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17631) = 3 ^ 9 * m + 10592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17631.1, data_15_17631.2]

/-- Complete interval computation for depth 15, residue 17632. -/
theorem bounds_15_17632 : exactInterval 15 17632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17632 : oddCount 17632 15 = 5 ∧ acceleratedOrbit 15 17632 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17632) = 3 ^ 5 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17632.1, data_15_17632.2]

/-- Complete interval computation for depth 15, residue 17633. -/
theorem bounds_15_17633 : exactInterval 15 17633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17633 : oddCount 17633 15 = 10 ∧ acceleratedOrbit 15 17633 = 31780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17633) = 3 ^ 10 * m + 31780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17633.1, data_15_17633.2]

/-- Complete interval computation for depth 15, residue 17634. -/
theorem bounds_15_17634 : exactInterval 15 17634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17634 : oddCount 17634 15 = 6 ∧ acceleratedOrbit 15 17634 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17634) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17634.1, data_15_17634.2]

/-- Complete interval computation for depth 15, residue 17635. -/
theorem bounds_15_17635 : exactInterval 15 17635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17635 : oddCount 17635 15 = 6 ∧ acceleratedOrbit 15 17635 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17635) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17635.1, data_15_17635.2]

/-- Complete interval computation for depth 15, residue 17636. -/
theorem bounds_15_17636 : exactInterval 15 17636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17636 : oddCount 17636 15 = 9 ∧ acceleratedOrbit 15 17636 = 10601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17636) = 3 ^ 9 * m + 10601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17636.1, data_15_17636.2]

/-- Complete interval computation for depth 15, residue 17637. -/
theorem bounds_15_17637 : exactInterval 15 17637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17637 : oddCount 17637 15 = 9 ∧ acceleratedOrbit 15 17637 = 10601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17637) = 3 ^ 9 * m + 10601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17637.1, data_15_17637.2]

/-- Complete interval computation for depth 15, residue 17638. -/
theorem bounds_15_17638 : exactInterval 15 17638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17638 : oddCount 17638 15 = 9 ∧ acceleratedOrbit 15 17638 = 10601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17638) = 3 ^ 9 * m + 10601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17638.1, data_15_17638.2]

/-- Complete interval computation for depth 15, residue 17639. -/
theorem bounds_15_17639 : exactInterval 15 17639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17639 : oddCount 17639 15 = 10 ∧ acceleratedOrbit 15 17639 = 31789 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17639) = 3 ^ 10 * m + 31789 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17639.1, data_15_17639.2]

/-- Complete interval computation for depth 15, residue 17640. -/
theorem bounds_15_17640 : exactInterval 15 17640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17640 : oddCount 17640 15 = 5 ∧ acceleratedOrbit 15 17640 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17640) = 3 ^ 5 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17640.1, data_15_17640.2]

/-- Complete interval computation for depth 15, residue 17641. -/
theorem bounds_15_17641 : exactInterval 15 17641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17641 : oddCount 17641 15 = 7 ∧ acceleratedOrbit 15 17641 = 1178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17641) = 3 ^ 7 * m + 1178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17641.1, data_15_17641.2]

/-- Complete interval computation for depth 15, residue 17642. -/
theorem bounds_15_17642 : exactInterval 15 17642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17642 : oddCount 17642 15 = 5 ∧ acceleratedOrbit 15 17642 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17642) = 3 ^ 5 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17642.1, data_15_17642.2]

/-- Complete interval computation for depth 15, residue 17643. -/
theorem bounds_15_17643 : exactInterval 15 17643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17643 : oddCount 17643 15 = 8 ∧ acceleratedOrbit 15 17643 = 3533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17643) = 3 ^ 8 * m + 3533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17643.1, data_15_17643.2]

/-- Complete interval computation for depth 15, residue 17644. -/
theorem bounds_15_17644 : exactInterval 15 17644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17644 : oddCount 17644 15 = 5 ∧ acceleratedOrbit 15 17644 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17644) = 3 ^ 5 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17644.1, data_15_17644.2]

/-- Complete interval computation for depth 15, residue 17645. -/
theorem bounds_15_17645 : exactInterval 15 17645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17645 : oddCount 17645 15 = 5 ∧ acceleratedOrbit 15 17645 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17645) = 3 ^ 5 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17645.1, data_15_17645.2]

/-- Complete interval computation for depth 15, residue 17646. -/
theorem bounds_15_17646 : exactInterval 15 17646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17646 : oddCount 17646 15 = 5 ∧ acceleratedOrbit 15 17646 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17646) = 3 ^ 5 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17646.1, data_15_17646.2]

/-- Complete interval computation for depth 15, residue 17647. -/
theorem bounds_15_17647 : exactInterval 15 17647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17647 : oddCount 17647 15 = 13 ∧ acceleratedOrbit 15 17647 = 858671 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17647) = 3 ^ 13 * m + 858671 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17647.1, data_15_17647.2]

/-- Complete interval computation for depth 15, residue 17648. -/
theorem bounds_15_17648 : exactInterval 15 17648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17648 : oddCount 17648 15 = 5 ∧ acceleratedOrbit 15 17648 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17648) = 3 ^ 5 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17648.1, data_15_17648.2]

/-- Complete interval computation for depth 15, residue 17649. -/
theorem bounds_15_17649 : exactInterval 15 17649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17649 : oddCount 17649 15 = 5 ∧ acceleratedOrbit 15 17649 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17649) = 3 ^ 5 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17649.1, data_15_17649.2]

/-- Complete interval computation for depth 15, residue 17650. -/
theorem bounds_15_17650 : exactInterval 15 17650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17650 : oddCount 17650 15 = 8 ∧ acceleratedOrbit 15 17650 = 3536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17650) = 3 ^ 8 * m + 3536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17650.1, data_15_17650.2]

/-- Complete interval computation for depth 15, residue 17651. -/
theorem bounds_15_17651 : exactInterval 15 17651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17651 : oddCount 17651 15 = 8 ∧ acceleratedOrbit 15 17651 = 3536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17651) = 3 ^ 8 * m + 3536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17651.1, data_15_17651.2]

/-- Complete interval computation for depth 15, residue 17652. -/
theorem bounds_15_17652 : exactInterval 15 17652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17652 : oddCount 17652 15 = 5 ∧ acceleratedOrbit 15 17652 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17652) = 3 ^ 5 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17652.1, data_15_17652.2]

/-- Complete interval computation for depth 15, residue 17653. -/
theorem bounds_15_17653 : exactInterval 15 17653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17653 : oddCount 17653 15 = 5 ∧ acceleratedOrbit 15 17653 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17653) = 3 ^ 5 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17653.1, data_15_17653.2]

/-- Complete interval computation for depth 15, residue 17654. -/
theorem bounds_15_17654 : exactInterval 15 17654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17654 : oddCount 17654 15 = 9 ∧ acceleratedOrbit 15 17654 = 10610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17654) = 3 ^ 9 * m + 10610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17654.1, data_15_17654.2]

/-- Complete interval computation for depth 15, residue 17655. -/
theorem bounds_15_17655 : exactInterval 15 17655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17655 : oddCount 17655 15 = 9 ∧ acceleratedOrbit 15 17655 = 10610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17655) = 3 ^ 9 * m + 10610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17655.1, data_15_17655.2]

/-- Complete interval computation for depth 15, residue 17656. -/
theorem bounds_15_17656 : exactInterval 15 17656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17656 : oddCount 17656 15 = 11 ∧ acceleratedOrbit 15 17656 = 95498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17656) = 3 ^ 11 * m + 95498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17656.1, data_15_17656.2]

/-- Complete interval computation for depth 15, residue 17657. -/
theorem bounds_15_17657 : exactInterval 15 17657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17657 : oddCount 17657 15 = 9 ∧ acceleratedOrbit 15 17657 = 10610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17657) = 3 ^ 9 * m + 10610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17657.1, data_15_17657.2]

/-- Complete interval computation for depth 15, residue 17658. -/
theorem bounds_15_17658 : exactInterval 15 17658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17658 : oddCount 17658 15 = 11 ∧ acceleratedOrbit 15 17658 = 95498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17658) = 3 ^ 11 * m + 95498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17658.1, data_15_17658.2]

/-- Complete interval computation for depth 15, residue 17659. -/
theorem bounds_15_17659 : exactInterval 15 17659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17659 : oddCount 17659 15 = 10 ∧ acceleratedOrbit 15 17659 = 31826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17659) = 3 ^ 10 * m + 31826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17659.1, data_15_17659.2]

/-- Complete interval computation for depth 15, residue 17660. -/
theorem bounds_15_17660 : exactInterval 15 17660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17660 : oddCount 17660 15 = 11 ∧ acceleratedOrbit 15 17660 = 95498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17660) = 3 ^ 11 * m + 95498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17660.1, data_15_17660.2]

end Collatz.Research.PassageAtlas.Batch0539
