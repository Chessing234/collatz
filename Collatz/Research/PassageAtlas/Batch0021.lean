import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0021

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 655. -/
theorem bounds_15_655 : exactInterval 15 655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_655 : oddCount 655 15 = 11 ∧ acceleratedOrbit 15 655 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 655) = 3 ^ 11 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_655.1, data_15_655.2]

/-- Complete interval computation for depth 15, residue 656. -/
theorem bounds_15_656 : exactInterval 15 656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_656 : oddCount 656 15 = 8 ∧ acceleratedOrbit 15 656 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 656) = 3 ^ 8 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_656.1, data_15_656.2]

/-- Complete interval computation for depth 15, residue 657. -/
theorem bounds_15_657 : exactInterval 15 657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_657 : oddCount 657 15 = 8 ∧ acceleratedOrbit 15 657 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 657) = 3 ^ 8 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_657.1, data_15_657.2]

/-- Complete interval computation for depth 15, residue 658. -/
theorem bounds_15_658 : exactInterval 15 658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_658 : oddCount 658 15 = 8 ∧ acceleratedOrbit 15 658 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 658) = 3 ^ 8 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_658.1, data_15_658.2]

/-- Complete interval computation for depth 15, residue 659. -/
theorem bounds_15_659 : exactInterval 15 659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_659 : oddCount 659 15 = 8 ∧ acceleratedOrbit 15 659 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 659) = 3 ^ 8 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_659.1, data_15_659.2]

/-- Complete interval computation for depth 15, residue 660. -/
theorem bounds_15_660 : exactInterval 15 660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_660 : oddCount 660 15 = 8 ∧ acceleratedOrbit 15 660 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 660) = 3 ^ 8 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_660.1, data_15_660.2]

/-- Complete interval computation for depth 15, residue 661. -/
theorem bounds_15_661 : exactInterval 15 661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_661 : oddCount 661 15 = 8 ∧ acceleratedOrbit 15 661 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 661) = 3 ^ 8 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_661.1, data_15_661.2]

/-- Complete interval computation for depth 15, residue 662. -/
theorem bounds_15_662 : exactInterval 15 662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_662 : oddCount 662 15 = 5 ∧ acceleratedOrbit 15 662 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 662) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_662.1, data_15_662.2]

/-- Complete interval computation for depth 15, residue 663. -/
theorem bounds_15_663 : exactInterval 15 663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_663 : oddCount 663 15 = 5 ∧ acceleratedOrbit 15 663 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 663) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_663.1, data_15_663.2]

/-- Complete interval computation for depth 15, residue 664. -/
theorem bounds_15_664 : exactInterval 15 664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_664 : oddCount 664 15 = 8 ∧ acceleratedOrbit 15 664 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 664) = 3 ^ 8 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_664.1, data_15_664.2]

/-- Complete interval computation for depth 15, residue 665. -/
theorem bounds_15_665 : exactInterval 15 665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_665 : oddCount 665 15 = 9 ∧ acceleratedOrbit 15 665 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 665) = 3 ^ 9 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_665.1, data_15_665.2]

/-- Complete interval computation for depth 15, residue 666. -/
theorem bounds_15_666 : exactInterval 15 666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_666 : oddCount 666 15 = 8 ∧ acceleratedOrbit 15 666 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 666) = 3 ^ 8 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_666.1, data_15_666.2]

/-- Complete interval computation for depth 15, residue 667. -/
theorem bounds_15_667 : exactInterval 15 667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_667 : oddCount 667 15 = 12 ∧ acceleratedOrbit 15 667 = 10844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 667) = 3 ^ 12 * m + 10844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_667.1, data_15_667.2]

/-- Complete interval computation for depth 15, residue 668. -/
theorem bounds_15_668 : exactInterval 15 668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_668 : oddCount 668 15 = 11 ∧ acceleratedOrbit 15 668 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 668) = 3 ^ 11 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_668.1, data_15_668.2]

/-- Complete interval computation for depth 15, residue 669. -/
theorem bounds_15_669 : exactInterval 15 669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_669 : oddCount 669 15 = 11 ∧ acceleratedOrbit 15 669 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 669) = 3 ^ 11 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_669.1, data_15_669.2]

/-- Complete interval computation for depth 15, residue 670. -/
theorem bounds_15_670 : exactInterval 15 670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_670 : oddCount 670 15 = 11 ∧ acceleratedOrbit 15 670 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 670) = 3 ^ 11 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_670.1, data_15_670.2]

/-- Complete interval computation for depth 15, residue 671. -/
theorem bounds_15_671 : exactInterval 15 671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_671 : oddCount 671 15 = 11 ∧ acceleratedOrbit 15 671 = 3635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 671) = 3 ^ 11 * m + 3635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_671.1, data_15_671.2]

/-- Complete interval computation for depth 15, residue 672. -/
theorem bounds_15_672 : exactInterval 15 672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_672 : oddCount 672 15 = 3 ∧ acceleratedOrbit 15 672 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 672) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_672.1, data_15_672.2]

/-- Complete interval computation for depth 15, residue 673. -/
theorem bounds_15_673 : exactInterval 15 673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_673 : oddCount 673 15 = 9 ∧ acceleratedOrbit 15 673 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 673) = 3 ^ 9 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_673.1, data_15_673.2]

/-- Complete interval computation for depth 15, residue 674. -/
theorem bounds_15_674 : exactInterval 15 674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_674 : oddCount 674 15 = 8 ∧ acceleratedOrbit 15 674 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 674) = 3 ^ 8 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_674.1, data_15_674.2]

/-- Complete interval computation for depth 15, residue 675. -/
theorem bounds_15_675 : exactInterval 15 675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_675 : oddCount 675 15 = 8 ∧ acceleratedOrbit 15 675 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 675) = 3 ^ 8 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_675.1, data_15_675.2]

/-- Complete interval computation for depth 15, residue 676. -/
theorem bounds_15_676 : exactInterval 15 676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_676 : oddCount 676 15 = 9 ∧ acceleratedOrbit 15 676 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 676) = 3 ^ 9 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_676.1, data_15_676.2]

/-- Complete interval computation for depth 15, residue 677. -/
theorem bounds_15_677 : exactInterval 15 677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_677 : oddCount 677 15 = 9 ∧ acceleratedOrbit 15 677 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 677) = 3 ^ 9 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_677.1, data_15_677.2]

/-- Complete interval computation for depth 15, residue 678. -/
theorem bounds_15_678 : exactInterval 15 678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_678 : oddCount 678 15 = 9 ∧ acceleratedOrbit 15 678 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 678) = 3 ^ 9 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_678.1, data_15_678.2]

/-- Complete interval computation for depth 15, residue 679. -/
theorem bounds_15_679 : exactInterval 15 679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_679 : oddCount 679 15 = 9 ∧ acceleratedOrbit 15 679 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 679) = 3 ^ 9 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_679.1, data_15_679.2]

/-- Complete interval computation for depth 15, residue 680. -/
theorem bounds_15_680 : exactInterval 15 680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_680 : oddCount 680 15 = 3 ∧ acceleratedOrbit 15 680 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 680) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_680.1, data_15_680.2]

/-- Complete interval computation for depth 15, residue 681. -/
theorem bounds_15_681 : exactInterval 15 681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_681 : oddCount 681 15 = 12 ∧ acceleratedOrbit 15 681 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 681) = 3 ^ 12 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_681.1, data_15_681.2]

/-- Complete interval computation for depth 15, residue 682. -/
theorem bounds_15_682 : exactInterval 15 682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_682 : oddCount 682 15 = 3 ∧ acceleratedOrbit 15 682 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 682) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_682.1, data_15_682.2]

/-- Complete interval computation for depth 15, residue 683. -/
theorem bounds_15_683 : exactInterval 15 683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_683 : oddCount 683 15 = 7 ∧ acceleratedOrbit 15 683 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 683) = 3 ^ 7 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_683.1, data_15_683.2]

/-- Complete interval computation for depth 15, residue 684. -/
theorem bounds_15_684 : exactInterval 15 684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_684 : oddCount 684 15 = 7 ∧ acceleratedOrbit 15 684 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 684) = 3 ^ 7 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_684.1, data_15_684.2]

/-- Complete interval computation for depth 15, residue 685. -/
theorem bounds_15_685 : exactInterval 15 685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_685 : oddCount 685 15 = 7 ∧ acceleratedOrbit 15 685 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 685) = 3 ^ 7 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_685.1, data_15_685.2]

/-- Complete interval computation for depth 15, residue 686. -/
theorem bounds_15_686 : exactInterval 15 686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_686 : oddCount 686 15 = 7 ∧ acceleratedOrbit 15 686 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 686) = 3 ^ 7 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_686.1, data_15_686.2]

/-- Complete interval computation for depth 15, residue 687. -/
theorem bounds_15_687 : exactInterval 15 687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_687 : oddCount 687 15 = 7 ∧ acceleratedOrbit 15 687 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 687) = 3 ^ 7 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_687.1, data_15_687.2]

end Collatz.Research.PassageAtlas.Batch0021
