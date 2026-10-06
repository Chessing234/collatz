import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0113

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 696. -/
theorem bounds_11_696 : exactInterval 11 696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_696 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 696) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_696 : oddCount 696 11 = 4 ∧ acceleratedOrbit 11 696 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_696 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 696) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_696.1, data_11_696.2]

/-- Complete interval computation for depth 11, residue 697. -/
theorem bounds_11_697 : exactInterval 11 697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_697 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 697) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_697 : oddCount 697 11 = 5 ∧ acceleratedOrbit 11 697 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_697 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 697) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_697.1, data_11_697.2]

/-- Complete interval computation for depth 11, residue 698. -/
theorem bounds_11_698 : exactInterval 11 698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_698 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 698) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_698 : oddCount 698 11 = 4 ∧ acceleratedOrbit 11 698 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_698 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 698) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_698.1, data_11_698.2]

/-- Complete interval computation for depth 11, residue 699. -/
theorem bounds_11_699 : exactInterval 11 699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_699 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 699) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_699 : oddCount 699 11 = 7 ∧ acceleratedOrbit 11 699 = 749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_699 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 699) = 3 ^ 7 * m + 749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_699.1, data_11_699.2]

/-- Complete interval computation for depth 11, residue 700. -/
theorem bounds_11_700 : exactInterval 11 700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_700 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 700) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_700 : oddCount 700 11 = 6 ∧ acceleratedOrbit 11 700 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_700 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 700) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_700.1, data_11_700.2]

/-- Complete interval computation for depth 11, residue 701. -/
theorem bounds_11_701 : exactInterval 11 701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_701 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 701) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_701 : oddCount 701 11 = 6 ∧ acceleratedOrbit 11 701 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_701 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 701) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_701.1, data_11_701.2]

/-- Complete interval computation for depth 11, residue 702. -/
theorem bounds_11_702 : exactInterval 11 702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_702 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 702) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_702 : oddCount 702 11 = 6 ∧ acceleratedOrbit 11 702 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_702 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 702) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_702.1, data_11_702.2]

/-- Complete interval computation for depth 11, residue 703. -/
theorem bounds_11_703 : exactInterval 11 703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_703 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 703) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_703 : oddCount 703 11 = 9 ∧ acceleratedOrbit 11 703 = 6767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_703 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 703) = 3 ^ 9 * m + 6767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_703.1, data_11_703.2]

/-- Complete interval computation for depth 11, residue 704. -/
theorem bounds_11_704 : exactInterval 11 704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_704 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 704) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_704 : oddCount 704 11 = 3 ∧ acceleratedOrbit 11 704 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_704 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 704) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_704.1, data_11_704.2]

/-- Complete interval computation for depth 11, residue 705. -/
theorem bounds_11_705 : exactInterval 11 705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_705 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 705) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_705 : oddCount 705 11 = 4 ∧ acceleratedOrbit 11 705 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_705 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 705) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_705.1, data_11_705.2]

/-- Complete interval computation for depth 11, residue 706. -/
theorem bounds_11_706 : exactInterval 11 706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_706 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 706) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_706 : oddCount 706 11 = 6 ∧ acceleratedOrbit 11 706 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_706 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 706) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_706.1, data_11_706.2]

/-- Complete interval computation for depth 11, residue 707. -/
theorem bounds_11_707 : exactInterval 11 707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_707 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 707) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_707 : oddCount 707 11 = 6 ∧ acceleratedOrbit 11 707 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_707 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 707) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_707.1, data_11_707.2]

/-- Complete interval computation for depth 11, residue 708. -/
theorem bounds_11_708 : exactInterval 11 708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_708 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 708) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_708 : oddCount 708 11 = 4 ∧ acceleratedOrbit 11 708 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_708 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 708) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_708.1, data_11_708.2]

/-- Complete interval computation for depth 11, residue 709. -/
theorem bounds_11_709 : exactInterval 11 709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_709 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 709) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_709 : oddCount 709 11 = 4 ∧ acceleratedOrbit 11 709 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_709 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 709) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_709.1, data_11_709.2]

/-- Complete interval computation for depth 11, residue 710. -/
theorem bounds_11_710 : exactInterval 11 710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_710 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 710) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_710 : oddCount 710 11 = 4 ∧ acceleratedOrbit 11 710 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_710 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 710) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_710.1, data_11_710.2]

end Collatz.Research.StoppingAtlas.Batch0113
