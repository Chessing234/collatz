import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0967

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31653. -/
theorem bounds_15_31653 : exactInterval 15 31653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31653 : oddCount 31653 15 = 7 ∧ acceleratedOrbit 15 31653 = 2113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31653) = 3 ^ 7 * m + 2113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31653.1, data_15_31653.2]

/-- Complete interval computation for depth 15, residue 31654. -/
theorem bounds_15_31654 : exactInterval 15 31654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31654 : oddCount 31654 15 = 7 ∧ acceleratedOrbit 15 31654 = 2113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31654) = 3 ^ 7 * m + 2113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31654.1, data_15_31654.2]

/-- Complete interval computation for depth 15, residue 31655. -/
theorem bounds_15_31655 : exactInterval 15 31655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31655 : oddCount 31655 15 = 9 ∧ acceleratedOrbit 15 31655 = 19016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31655) = 3 ^ 9 * m + 19016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31655.1, data_15_31655.2]

/-- Complete interval computation for depth 15, residue 31656. -/
theorem bounds_15_31656 : exactInterval 15 31656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31656 : oddCount 31656 15 = 5 ∧ acceleratedOrbit 15 31656 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31656) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31656.1, data_15_31656.2]

/-- Complete interval computation for depth 15, residue 31657. -/
theorem bounds_15_31657 : exactInterval 15 31657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31657 : oddCount 31657 15 = 11 ∧ acceleratedOrbit 15 31657 = 171152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31657) = 3 ^ 11 * m + 171152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31657.1, data_15_31657.2]

/-- Complete interval computation for depth 15, residue 31658. -/
theorem bounds_15_31658 : exactInterval 15 31658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31658 : oddCount 31658 15 = 5 ∧ acceleratedOrbit 15 31658 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31658) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31658.1, data_15_31658.2]

/-- Complete interval computation for depth 15, residue 31659. -/
theorem bounds_15_31659 : exactInterval 15 31659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31659 : oddCount 31659 15 = 8 ∧ acceleratedOrbit 15 31659 = 6340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31659) = 3 ^ 8 * m + 6340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31659.1, data_15_31659.2]

/-- Complete interval computation for depth 15, residue 31660. -/
theorem bounds_15_31660 : exactInterval 15 31660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31660 : oddCount 31660 15 = 7 ∧ acceleratedOrbit 15 31660 = 2114 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31660) = 3 ^ 7 * m + 2114 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31660.1, data_15_31660.2]

/-- Complete interval computation for depth 15, residue 31661. -/
theorem bounds_15_31661 : exactInterval 15 31661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31661 : oddCount 31661 15 = 7 ∧ acceleratedOrbit 15 31661 = 2114 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31661) = 3 ^ 7 * m + 2114 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31661.1, data_15_31661.2]

/-- Complete interval computation for depth 15, residue 31662. -/
theorem bounds_15_31662 : exactInterval 15 31662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31662 : oddCount 31662 15 = 7 ∧ acceleratedOrbit 15 31662 = 2114 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31662) = 3 ^ 7 * m + 2114 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31662.1, data_15_31662.2]

/-- Complete interval computation for depth 15, residue 31663. -/
theorem bounds_15_31663 : exactInterval 15 31663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31663 : oddCount 31663 15 = 7 ∧ acceleratedOrbit 15 31663 = 2114 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31663) = 3 ^ 7 * m + 2114 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31663.1, data_15_31663.2]

/-- Complete interval computation for depth 15, residue 31664. -/
theorem bounds_15_31664 : exactInterval 15 31664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31664 : oddCount 31664 15 = 5 ∧ acceleratedOrbit 15 31664 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31664) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31664.1, data_15_31664.2]

/-- Complete interval computation for depth 15, residue 31665. -/
theorem bounds_15_31665 : exactInterval 15 31665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31665 : oddCount 31665 15 = 5 ∧ acceleratedOrbit 15 31665 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31665) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31665.1, data_15_31665.2]

/-- Complete interval computation for depth 15, residue 31666. -/
theorem bounds_15_31666 : exactInterval 15 31666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31666 : oddCount 31666 15 = 5 ∧ acceleratedOrbit 15 31666 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31666) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31666.1, data_15_31666.2]

/-- Complete interval computation for depth 15, residue 31667. -/
theorem bounds_15_31667 : exactInterval 15 31667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31667 : oddCount 31667 15 = 5 ∧ acceleratedOrbit 15 31667 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31667) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31667.1, data_15_31667.2]

/-- Complete interval computation for depth 15, residue 31668. -/
theorem bounds_15_31668 : exactInterval 15 31668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31668 : oddCount 31668 15 = 5 ∧ acceleratedOrbit 15 31668 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31668) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31668.1, data_15_31668.2]

/-- Complete interval computation for depth 15, residue 31669. -/
theorem bounds_15_31669 : exactInterval 15 31669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31669 : oddCount 31669 15 = 5 ∧ acceleratedOrbit 15 31669 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31669) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31669.1, data_15_31669.2]

/-- Complete interval computation for depth 15, residue 31670. -/
theorem bounds_15_31670 : exactInterval 15 31670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31670 : oddCount 31670 15 = 8 ∧ acceleratedOrbit 15 31670 = 6344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31670) = 3 ^ 8 * m + 6344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31670.1, data_15_31670.2]

/-- Complete interval computation for depth 15, residue 31671. -/
theorem bounds_15_31671 : exactInterval 15 31671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31671 : oddCount 31671 15 = 8 ∧ acceleratedOrbit 15 31671 = 6344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31671) = 3 ^ 8 * m + 6344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31671.1, data_15_31671.2]

/-- Complete interval computation for depth 15, residue 31672. -/
theorem bounds_15_31672 : exactInterval 15 31672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31672 : oddCount 31672 15 = 5 ∧ acceleratedOrbit 15 31672 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31672) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31672.1, data_15_31672.2]

/-- Complete interval computation for depth 15, residue 31673. -/
theorem bounds_15_31673 : exactInterval 15 31673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31673 : oddCount 31673 15 = 8 ∧ acceleratedOrbit 15 31673 = 6344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31673) = 3 ^ 8 * m + 6344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31673.1, data_15_31673.2]

/-- Complete interval computation for depth 15, residue 31674. -/
theorem bounds_15_31674 : exactInterval 15 31674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31674 : oddCount 31674 15 = 5 ∧ acceleratedOrbit 15 31674 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31674) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31674.1, data_15_31674.2]

/-- Complete interval computation for depth 15, residue 31675. -/
theorem bounds_15_31675 : exactInterval 15 31675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31675 : oddCount 31675 15 = 8 ∧ acceleratedOrbit 15 31675 = 6344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31675) = 3 ^ 8 * m + 6344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31675.1, data_15_31675.2]

/-- Complete interval computation for depth 15, residue 31676. -/
theorem bounds_15_31676 : exactInterval 15 31676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31676 : oddCount 31676 15 = 9 ∧ acceleratedOrbit 15 31676 = 19030 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31676) = 3 ^ 9 * m + 19030 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31676.1, data_15_31676.2]

/-- Complete interval computation for depth 15, residue 31677. -/
theorem bounds_15_31677 : exactInterval 15 31677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31677 : oddCount 31677 15 = 9 ∧ acceleratedOrbit 15 31677 = 19030 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31677) = 3 ^ 9 * m + 19030 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31677.1, data_15_31677.2]

/-- Complete interval computation for depth 15, residue 31678. -/
theorem bounds_15_31678 : exactInterval 15 31678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31678 : oddCount 31678 15 = 9 ∧ acceleratedOrbit 15 31678 = 19030 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31678) = 3 ^ 9 * m + 19030 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31678.1, data_15_31678.2]

/-- Complete interval computation for depth 15, residue 31679. -/
theorem bounds_15_31679 : exactInterval 15 31679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31679 : oddCount 31679 15 = 10 ∧ acceleratedOrbit 15 31679 = 57089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31679) = 3 ^ 10 * m + 57089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31679.1, data_15_31679.2]

/-- Complete interval computation for depth 15, residue 31680. -/
theorem bounds_15_31680 : exactInterval 15 31680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31680 : oddCount 31680 15 = 7 ∧ acceleratedOrbit 15 31680 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31680) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31680.1, data_15_31680.2]

/-- Complete interval computation for depth 15, residue 31681. -/
theorem bounds_15_31681 : exactInterval 15 31681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31681 : oddCount 31681 15 = 10 ∧ acceleratedOrbit 15 31681 = 57104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31681) = 3 ^ 10 * m + 57104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31681.1, data_15_31681.2]

/-- Complete interval computation for depth 15, residue 31682. -/
theorem bounds_15_31682 : exactInterval 15 31682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31682 : oddCount 31682 15 = 10 ∧ acceleratedOrbit 15 31682 = 57104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31682) = 3 ^ 10 * m + 57104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31682.1, data_15_31682.2]

/-- Complete interval computation for depth 15, residue 31683. -/
theorem bounds_15_31683 : exactInterval 15 31683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31683 : oddCount 31683 15 = 10 ∧ acceleratedOrbit 15 31683 = 57104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31683) = 3 ^ 10 * m + 57104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31683.1, data_15_31683.2]

/-- Complete interval computation for depth 15, residue 31684. -/
theorem bounds_15_31684 : exactInterval 15 31684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31684 : oddCount 31684 15 = 5 ∧ acceleratedOrbit 15 31684 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31684) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31684.1, data_15_31684.2]

/-- Complete interval computation for depth 15, residue 31685. -/
theorem bounds_15_31685 : exactInterval 15 31685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31685 : oddCount 31685 15 = 5 ∧ acceleratedOrbit 15 31685 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31685) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31685.1, data_15_31685.2]

end Collatz.Research.PassageAtlas.Batch0967
