import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0022

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 688. -/
theorem bounds_15_688 : exactInterval 15 688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_688 : oddCount 688 15 = 6 ∧ acceleratedOrbit 15 688 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 688) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_688.1, data_15_688.2]

/-- Complete interval computation for depth 15, residue 689. -/
theorem bounds_15_689 : exactInterval 15 689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_689 : oddCount 689 15 = 7 ∧ acceleratedOrbit 15 689 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 689) = 3 ^ 7 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_689.1, data_15_689.2]

/-- Complete interval computation for depth 15, residue 690. -/
theorem bounds_15_690 : exactInterval 15 690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_690 : oddCount 690 15 = 7 ∧ acceleratedOrbit 15 690 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 690) = 3 ^ 7 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_690.1, data_15_690.2]

/-- Complete interval computation for depth 15, residue 691. -/
theorem bounds_15_691 : exactInterval 15 691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_691 : oddCount 691 15 = 7 ∧ acceleratedOrbit 15 691 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 691) = 3 ^ 7 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_691.1, data_15_691.2]

/-- Complete interval computation for depth 15, residue 692. -/
theorem bounds_15_692 : exactInterval 15 692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_692 : oddCount 692 15 = 6 ∧ acceleratedOrbit 15 692 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 692) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_692.1, data_15_692.2]

/-- Complete interval computation for depth 15, residue 693. -/
theorem bounds_15_693 : exactInterval 15 693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_693 : oddCount 693 15 = 6 ∧ acceleratedOrbit 15 693 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 693) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_693.1, data_15_693.2]

/-- Complete interval computation for depth 15, residue 694. -/
theorem bounds_15_694 : exactInterval 15 694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_694 : oddCount 694 15 = 7 ∧ acceleratedOrbit 15 694 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 694) = 3 ^ 7 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_694.1, data_15_694.2]

/-- Complete interval computation for depth 15, residue 695. -/
theorem bounds_15_695 : exactInterval 15 695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_695 : oddCount 695 15 = 7 ∧ acceleratedOrbit 15 695 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 695) = 3 ^ 7 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_695.1, data_15_695.2]

/-- Complete interval computation for depth 15, residue 696. -/
theorem bounds_15_696 : exactInterval 15 696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_696 : oddCount 696 15 = 6 ∧ acceleratedOrbit 15 696 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 696) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_696.1, data_15_696.2]

/-- Complete interval computation for depth 15, residue 697. -/
theorem bounds_15_697 : exactInterval 15 697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_697 : oddCount 697 15 = 7 ∧ acceleratedOrbit 15 697 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 697) = 3 ^ 7 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_697.1, data_15_697.2]

/-- Complete interval computation for depth 15, residue 698. -/
theorem bounds_15_698 : exactInterval 15 698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_698 : oddCount 698 15 = 6 ∧ acceleratedOrbit 15 698 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 698) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_698.1, data_15_698.2]

/-- Complete interval computation for depth 15, residue 699. -/
theorem bounds_15_699 : exactInterval 15 699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_699 : oddCount 699 15 = 9 ∧ acceleratedOrbit 15 699 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 699) = 3 ^ 9 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_699.1, data_15_699.2]

/-- Complete interval computation for depth 15, residue 700. -/
theorem bounds_15_700 : exactInterval 15 700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_700 : oddCount 700 15 = 9 ∧ acceleratedOrbit 15 700 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 700) = 3 ^ 9 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_700.1, data_15_700.2]

/-- Complete interval computation for depth 15, residue 701. -/
theorem bounds_15_701 : exactInterval 15 701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_701 : oddCount 701 15 = 9 ∧ acceleratedOrbit 15 701 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 701) = 3 ^ 9 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_701.1, data_15_701.2]

/-- Complete interval computation for depth 15, residue 702. -/
theorem bounds_15_702 : exactInterval 15 702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_702 : oddCount 702 15 = 9 ∧ acceleratedOrbit 15 702 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 702) = 3 ^ 9 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_702.1, data_15_702.2]

/-- Complete interval computation for depth 15, residue 703. -/
theorem bounds_15_703 : exactInterval 15 703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_703 : oddCount 703 15 = 13 ∧ acceleratedOrbit 15 703 = 34262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 703) = 3 ^ 13 * m + 34262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_703.1, data_15_703.2]

/-- Complete interval computation for depth 15, residue 704. -/
theorem bounds_15_704 : exactInterval 15 704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_704 : oddCount 704 15 = 4 ∧ acceleratedOrbit 15 704 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 704) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_704.1, data_15_704.2]

/-- Complete interval computation for depth 15, residue 705. -/
theorem bounds_15_705 : exactInterval 15 705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_705 : oddCount 705 15 = 6 ∧ acceleratedOrbit 15 705 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 705) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_705.1, data_15_705.2]

/-- Complete interval computation for depth 15, residue 706. -/
theorem bounds_15_706 : exactInterval 15 706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_706 : oddCount 706 15 = 8 ∧ acceleratedOrbit 15 706 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 706) = 3 ^ 8 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_706.1, data_15_706.2]

/-- Complete interval computation for depth 15, residue 707. -/
theorem bounds_15_707 : exactInterval 15 707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_707 : oddCount 707 15 = 8 ∧ acceleratedOrbit 15 707 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 707) = 3 ^ 8 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_707.1, data_15_707.2]

/-- Complete interval computation for depth 15, residue 708. -/
theorem bounds_15_708 : exactInterval 15 708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_708 : oddCount 708 15 = 6 ∧ acceleratedOrbit 15 708 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 708) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_708.1, data_15_708.2]

/-- Complete interval computation for depth 15, residue 709. -/
theorem bounds_15_709 : exactInterval 15 709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_709 : oddCount 709 15 = 6 ∧ acceleratedOrbit 15 709 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 709) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_709.1, data_15_709.2]

/-- Complete interval computation for depth 15, residue 710. -/
theorem bounds_15_710 : exactInterval 15 710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_710 : oddCount 710 15 = 6 ∧ acceleratedOrbit 15 710 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 710) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_710.1, data_15_710.2]

/-- Complete interval computation for depth 15, residue 711. -/
theorem bounds_15_711 : exactInterval 15 711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_711 : oddCount 711 15 = 9 ∧ acceleratedOrbit 15 711 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 711) = 3 ^ 9 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_711.1, data_15_711.2]

/-- Complete interval computation for depth 15, residue 712. -/
theorem bounds_15_712 : exactInterval 15 712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_712 : oddCount 712 15 = 6 ∧ acceleratedOrbit 15 712 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 712) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_712.1, data_15_712.2]

/-- Complete interval computation for depth 15, residue 713. -/
theorem bounds_15_713 : exactInterval 15 713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_713 : oddCount 713 15 = 6 ∧ acceleratedOrbit 15 713 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 713) = 3 ^ 6 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_713.1, data_15_713.2]

/-- Complete interval computation for depth 15, residue 714. -/
theorem bounds_15_714 : exactInterval 15 714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_714 : oddCount 714 15 = 6 ∧ acceleratedOrbit 15 714 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 714) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_714.1, data_15_714.2]

/-- Complete interval computation for depth 15, residue 715. -/
theorem bounds_15_715 : exactInterval 15 715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_715 : oddCount 715 15 = 6 ∧ acceleratedOrbit 15 715 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 715) = 3 ^ 6 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_715.1, data_15_715.2]

/-- Complete interval computation for depth 15, residue 716. -/
theorem bounds_15_716 : exactInterval 15 716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_716 : oddCount 716 15 = 6 ∧ acceleratedOrbit 15 716 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 716) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_716.1, data_15_716.2]

/-- Complete interval computation for depth 15, residue 717. -/
theorem bounds_15_717 : exactInterval 15 717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_717 : oddCount 717 15 = 6 ∧ acceleratedOrbit 15 717 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 717) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_717.1, data_15_717.2]

/-- Complete interval computation for depth 15, residue 718. -/
theorem bounds_15_718 : exactInterval 15 718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_718 : oddCount 718 15 = 9 ∧ acceleratedOrbit 15 718 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 718) = 3 ^ 9 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_718.1, data_15_718.2]

/-- Complete interval computation for depth 15, residue 719. -/
theorem bounds_15_719 : exactInterval 15 719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_719 : oddCount 719 15 = 9 ∧ acceleratedOrbit 15 719 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 719) = 3 ^ 9 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_719.1, data_15_719.2]

end Collatz.Research.PassageAtlas.Batch0022
