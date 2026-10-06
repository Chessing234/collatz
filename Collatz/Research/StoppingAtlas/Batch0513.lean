import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0513

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 696. -/
theorem bounds_13_696 : exactInterval 13 696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_696 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 696) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_696 : oddCount 696 13 = 4 ∧ acceleratedOrbit 13 696 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_696 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 696) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_696.1, data_13_696.2]

/-- Complete interval computation for depth 13, residue 697. -/
theorem bounds_13_697 : exactInterval 13 697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_697 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 697) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_697 : oddCount 697 13 = 7 ∧ acceleratedOrbit 13 697 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_697 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 697) = 3 ^ 7 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_697.1, data_13_697.2]

/-- Complete interval computation for depth 13, residue 698. -/
theorem bounds_13_698 : exactInterval 13 698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_698 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 698) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_698 : oddCount 698 13 = 4 ∧ acceleratedOrbit 13 698 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_698 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 698) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_698.1, data_13_698.2]

/-- Complete interval computation for depth 13, residue 699. -/
theorem bounds_13_699 : exactInterval 13 699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_699 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 699) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_699 : oddCount 699 13 = 8 ∧ acceleratedOrbit 13 699 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_699 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 699) = 3 ^ 8 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_699.1, data_13_699.2]

/-- Complete interval computation for depth 13, residue 700. -/
theorem bounds_13_700 : exactInterval 13 700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_700 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 700) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_700 : oddCount 700 13 = 8 ∧ acceleratedOrbit 13 700 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_700 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 700) = 3 ^ 8 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_700.1, data_13_700.2]

/-- Complete interval computation for depth 13, residue 701. -/
theorem bounds_13_701 : exactInterval 13 701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_701 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 701) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_701 : oddCount 701 13 = 8 ∧ acceleratedOrbit 13 701 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_701 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 701) = 3 ^ 8 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_701.1, data_13_701.2]

/-- Complete interval computation for depth 13, residue 702. -/
theorem bounds_13_702 : exactInterval 13 702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_702 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 702) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_702 : oddCount 702 13 = 8 ∧ acceleratedOrbit 13 702 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_702 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 702) = 3 ^ 8 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_702.1, data_13_702.2]

/-- Complete interval computation for depth 13, residue 703. -/
theorem bounds_13_703 : exactInterval 13 703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_703 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 703) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_703 : oddCount 703 13 = 11 ∧ acceleratedOrbit 13 703 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_703 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 703) = 3 ^ 11 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_703.1, data_13_703.2]

/-- Complete interval computation for depth 13, residue 704. -/
theorem bounds_13_704 : exactInterval 13 704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_704 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 704) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_704 : oddCount 704 13 = 4 ∧ acceleratedOrbit 13 704 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_704 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 704) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_704.1, data_13_704.2]

/-- Complete interval computation for depth 13, residue 705. -/
theorem bounds_13_705 : exactInterval 13 705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_705 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 705) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_705 : oddCount 705 13 = 4 ∧ acceleratedOrbit 13 705 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_705 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 705) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_705.1, data_13_705.2]

/-- Complete interval computation for depth 13, residue 706. -/
theorem bounds_13_706 : exactInterval 13 706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_706 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 706) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_706 : oddCount 706 13 = 7 ∧ acceleratedOrbit 13 706 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_706 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 706) = 3 ^ 7 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_706.1, data_13_706.2]

/-- Complete interval computation for depth 13, residue 707. -/
theorem bounds_13_707 : exactInterval 13 707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_707 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 707) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_707 : oddCount 707 13 = 7 ∧ acceleratedOrbit 13 707 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_707 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 707) = 3 ^ 7 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_707.1, data_13_707.2]

/-- Complete interval computation for depth 13, residue 708. -/
theorem bounds_13_708 : exactInterval 13 708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_708 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 708) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_708 : oddCount 708 13 = 5 ∧ acceleratedOrbit 13 708 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_708 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 708) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_708.1, data_13_708.2]

/-- Complete interval computation for depth 13, residue 709. -/
theorem bounds_13_709 : exactInterval 13 709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_709 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 709) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_709 : oddCount 709 13 = 5 ∧ acceleratedOrbit 13 709 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_709 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 709) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_709.1, data_13_709.2]

/-- Complete interval computation for depth 13, residue 710. -/
theorem bounds_13_710 : exactInterval 13 710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_710 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 710) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_710 : oddCount 710 13 = 5 ∧ acceleratedOrbit 13 710 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_710 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 710) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_710.1, data_13_710.2]

end Collatz.Research.StoppingAtlas.Batch0513
