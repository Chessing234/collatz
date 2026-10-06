import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0692

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22642. -/
theorem bounds_15_22642 : exactInterval 15 22642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22642 : oddCount 22642 15 = 9 ∧ acceleratedOrbit 15 22642 = 13607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22642) = 3 ^ 9 * m + 13607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22642.1, data_15_22642.2]

/-- Complete interval computation for depth 15, residue 22643. -/
theorem bounds_15_22643 : exactInterval 15 22643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22643 : oddCount 22643 15 = 9 ∧ acceleratedOrbit 15 22643 = 13607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22643) = 3 ^ 9 * m + 13607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22643.1, data_15_22643.2]

/-- Complete interval computation for depth 15, residue 22644. -/
theorem bounds_15_22644 : exactInterval 15 22644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22644 : oddCount 22644 15 = 4 ∧ acceleratedOrbit 15 22644 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22644) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22644.1, data_15_22644.2]

/-- Complete interval computation for depth 15, residue 22645. -/
theorem bounds_15_22645 : exactInterval 15 22645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22645 : oddCount 22645 15 = 4 ∧ acceleratedOrbit 15 22645 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22645) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22645.1, data_15_22645.2]

/-- Complete interval computation for depth 15, residue 22646. -/
theorem bounds_15_22646 : exactInterval 15 22646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22646 : oddCount 22646 15 = 10 ∧ acceleratedOrbit 15 22646 = 40823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22646) = 3 ^ 10 * m + 40823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22646.1, data_15_22646.2]

/-- Complete interval computation for depth 15, residue 22647. -/
theorem bounds_15_22647 : exactInterval 15 22647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22647 : oddCount 22647 15 = 10 ∧ acceleratedOrbit 15 22647 = 40823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22647) = 3 ^ 10 * m + 40823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22647.1, data_15_22647.2]

/-- Complete interval computation for depth 15, residue 22648. -/
theorem bounds_15_22648 : exactInterval 15 22648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22648 : oddCount 22648 15 = 4 ∧ acceleratedOrbit 15 22648 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22648) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22648.1, data_15_22648.2]

/-- Complete interval computation for depth 15, residue 22649. -/
theorem bounds_15_22649 : exactInterval 15 22649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22649 : oddCount 22649 15 = 10 ∧ acceleratedOrbit 15 22649 = 40819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22649) = 3 ^ 10 * m + 40819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22649.1, data_15_22649.2]

/-- Complete interval computation for depth 15, residue 22650. -/
theorem bounds_15_22650 : exactInterval 15 22650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22650 : oddCount 22650 15 = 4 ∧ acceleratedOrbit 15 22650 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22650) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22650.1, data_15_22650.2]

/-- Complete interval computation for depth 15, residue 22651. -/
theorem bounds_15_22651 : exactInterval 15 22651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22651 : oddCount 22651 15 = 11 ∧ acceleratedOrbit 15 22651 = 122471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22651) = 3 ^ 11 * m + 122471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22651.1, data_15_22651.2]

/-- Complete interval computation for depth 15, residue 22652. -/
theorem bounds_15_22652 : exactInterval 15 22652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22652 : oddCount 22652 15 = 9 ∧ acceleratedOrbit 15 22652 = 13610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22652) = 3 ^ 9 * m + 13610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22652.1, data_15_22652.2]

/-- Complete interval computation for depth 15, residue 22653. -/
theorem bounds_15_22653 : exactInterval 15 22653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22653 : oddCount 22653 15 = 9 ∧ acceleratedOrbit 15 22653 = 13610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22653) = 3 ^ 9 * m + 13610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22653.1, data_15_22653.2]

/-- Complete interval computation for depth 15, residue 22654. -/
theorem bounds_15_22654 : exactInterval 15 22654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22654 : oddCount 22654 15 = 9 ∧ acceleratedOrbit 15 22654 = 13610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22654) = 3 ^ 9 * m + 13610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22654.1, data_15_22654.2]

/-- Complete interval computation for depth 15, residue 22655. -/
theorem bounds_15_22655 : exactInterval 15 22655 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22655) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22655 : oddCount 22655 15 = 9 ∧ acceleratedOrbit 15 22655 = 13609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22655) = 3 ^ 9 * m + 13609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22655.1, data_15_22655.2]

/-- Complete interval computation for depth 15, residue 22656. -/
theorem bounds_15_22656 : exactInterval 15 22656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22656 : oddCount 22656 15 = 3 ∧ acceleratedOrbit 15 22656 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22656) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22656.1, data_15_22656.2]

/-- Complete interval computation for depth 15, residue 22657. -/
theorem bounds_15_22657 : exactInterval 15 22657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22657 : oddCount 22657 15 = 8 ∧ acceleratedOrbit 15 22657 = 4538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22657) = 3 ^ 8 * m + 4538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22657.1, data_15_22657.2]

/-- Complete interval computation for depth 15, residue 22658. -/
theorem bounds_15_22658 : exactInterval 15 22658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22658 : oddCount 22658 15 = 7 ∧ acceleratedOrbit 15 22658 = 1514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22658) = 3 ^ 7 * m + 1514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22658.1, data_15_22658.2]

/-- Complete interval computation for depth 15, residue 22659. -/
theorem bounds_15_22659 : exactInterval 15 22659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22659 : oddCount 22659 15 = 7 ∧ acceleratedOrbit 15 22659 = 1514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22659) = 3 ^ 7 * m + 1514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22659.1, data_15_22659.2]

/-- Complete interval computation for depth 15, residue 22660. -/
theorem bounds_15_22660 : exactInterval 15 22660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22660 : oddCount 22660 15 = 7 ∧ acceleratedOrbit 15 22660 = 1514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22660) = 3 ^ 7 * m + 1514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22660.1, data_15_22660.2]

/-- Complete interval computation for depth 15, residue 22661. -/
theorem bounds_15_22661 : exactInterval 15 22661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22661 : oddCount 22661 15 = 7 ∧ acceleratedOrbit 15 22661 = 1514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22661) = 3 ^ 7 * m + 1514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22661.1, data_15_22661.2]

/-- Complete interval computation for depth 15, residue 22662. -/
theorem bounds_15_22662 : exactInterval 15 22662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22662 : oddCount 22662 15 = 7 ∧ acceleratedOrbit 15 22662 = 1514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22662) = 3 ^ 7 * m + 1514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22662.1, data_15_22662.2]

/-- Complete interval computation for depth 15, residue 22663. -/
theorem bounds_15_22663 : exactInterval 15 22663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22663 : oddCount 22663 15 = 7 ∧ acceleratedOrbit 15 22663 = 1513 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22663) = 3 ^ 7 * m + 1513 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22663.1, data_15_22663.2]

/-- Complete interval computation for depth 15, residue 22664. -/
theorem bounds_15_22664 : exactInterval 15 22664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22664 : oddCount 22664 15 = 6 ∧ acceleratedOrbit 15 22664 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22664) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22664.1, data_15_22664.2]

/-- Complete interval computation for depth 15, residue 22665. -/
theorem bounds_15_22665 : exactInterval 15 22665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22665 : oddCount 22665 15 = 9 ∧ acceleratedOrbit 15 22665 = 13616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22665) = 3 ^ 9 * m + 13616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22665.1, data_15_22665.2]

/-- Complete interval computation for depth 15, residue 22666. -/
theorem bounds_15_22666 : exactInterval 15 22666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22666 : oddCount 22666 15 = 6 ∧ acceleratedOrbit 15 22666 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22666) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22666.1, data_15_22666.2]

/-- Complete interval computation for depth 15, residue 22667. -/
theorem bounds_15_22667 : exactInterval 15 22667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22667 : oddCount 22667 15 = 9 ∧ acceleratedOrbit 15 22667 = 13618 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22667) = 3 ^ 9 * m + 13618 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22667.1, data_15_22667.2]

/-- Complete interval computation for depth 15, residue 22668. -/
theorem bounds_15_22668 : exactInterval 15 22668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22668 : oddCount 22668 15 = 6 ∧ acceleratedOrbit 15 22668 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22668) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22668.1, data_15_22668.2]

/-- Complete interval computation for depth 15, residue 22669. -/
theorem bounds_15_22669 : exactInterval 15 22669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22669 : oddCount 22669 15 = 6 ∧ acceleratedOrbit 15 22669 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22669) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22669.1, data_15_22669.2]

/-- Complete interval computation for depth 15, residue 22670. -/
theorem bounds_15_22670 : exactInterval 15 22670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22670 : oddCount 22670 15 = 8 ∧ acceleratedOrbit 15 22670 = 4540 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22670) = 3 ^ 8 * m + 4540 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22670.1, data_15_22670.2]

/-- Complete interval computation for depth 15, residue 22671. -/
theorem bounds_15_22671 : exactInterval 15 22671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22671 : oddCount 22671 15 = 8 ∧ acceleratedOrbit 15 22671 = 4540 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22671) = 3 ^ 8 * m + 4540 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22671.1, data_15_22671.2]

/-- Complete interval computation for depth 15, residue 22672. -/
theorem bounds_15_22672 : exactInterval 15 22672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22672 : oddCount 22672 15 = 6 ∧ acceleratedOrbit 15 22672 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22672) = 3 ^ 6 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22672.1, data_15_22672.2]

/-- Complete interval computation for depth 15, residue 22673. -/
theorem bounds_15_22673 : exactInterval 15 22673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22673 : oddCount 22673 15 = 8 ∧ acceleratedOrbit 15 22673 = 4541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22673) = 3 ^ 8 * m + 4541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22673.1, data_15_22673.2]

/-- Complete interval computation for depth 15, residue 22674. -/
theorem bounds_15_22674 : exactInterval 15 22674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22674 : oddCount 22674 15 = 8 ∧ acceleratedOrbit 15 22674 = 4541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22674) = 3 ^ 8 * m + 4541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22674.1, data_15_22674.2]

end Collatz.Research.PassageAtlas.Batch0692
