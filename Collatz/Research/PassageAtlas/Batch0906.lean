import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0906

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29655. -/
theorem bounds_15_29655 : exactInterval 15 29655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29655 : oddCount 29655 15 = 9 ∧ acceleratedOrbit 15 29655 = 17815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29655) = 3 ^ 9 * m + 17815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29655.1, data_15_29655.2]

/-- Complete interval computation for depth 15, residue 29656. -/
theorem bounds_15_29656 : exactInterval 15 29656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29656 : oddCount 29656 15 = 5 ∧ acceleratedOrbit 15 29656 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29656) = 3 ^ 5 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29656.1, data_15_29656.2]

/-- Complete interval computation for depth 15, residue 29657. -/
theorem bounds_15_29657 : exactInterval 15 29657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29657 : oddCount 29657 15 = 6 ∧ acceleratedOrbit 15 29657 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29657) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29657.1, data_15_29657.2]

/-- Complete interval computation for depth 15, residue 29658. -/
theorem bounds_15_29658 : exactInterval 15 29658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29658 : oddCount 29658 15 = 5 ∧ acceleratedOrbit 15 29658 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29658) = 3 ^ 5 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29658.1, data_15_29658.2]

/-- Complete interval computation for depth 15, residue 29659. -/
theorem bounds_15_29659 : exactInterval 15 29659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29659 : oddCount 29659 15 = 9 ∧ acceleratedOrbit 15 29659 = 17819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29659) = 3 ^ 9 * m + 17819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29659.1, data_15_29659.2]

/-- Complete interval computation for depth 15, residue 29660. -/
theorem bounds_15_29660 : exactInterval 15 29660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29660 : oddCount 29660 15 = 5 ∧ acceleratedOrbit 15 29660 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29660) = 3 ^ 5 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29660.1, data_15_29660.2]

/-- Complete interval computation for depth 15, residue 29661. -/
theorem bounds_15_29661 : exactInterval 15 29661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29661 : oddCount 29661 15 = 5 ∧ acceleratedOrbit 15 29661 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29661) = 3 ^ 5 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29661.1, data_15_29661.2]

/-- Complete interval computation for depth 15, residue 29662. -/
theorem bounds_15_29662 : exactInterval 15 29662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29662 : oddCount 29662 15 = 11 ∧ acceleratedOrbit 15 29662 = 160370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29662) = 3 ^ 11 * m + 160370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29662.1, data_15_29662.2]

/-- Complete interval computation for depth 15, residue 29663. -/
theorem bounds_15_29663 : exactInterval 15 29663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29663 : oddCount 29663 15 = 11 ∧ acceleratedOrbit 15 29663 = 160370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29663) = 3 ^ 11 * m + 160370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29663.1, data_15_29663.2]

/-- Complete interval computation for depth 15, residue 29664. -/
theorem bounds_15_29664 : exactInterval 15 29664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29664 : oddCount 29664 15 = 7 ∧ acceleratedOrbit 15 29664 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29664) = 3 ^ 7 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29664.1, data_15_29664.2]

/-- Complete interval computation for depth 15, residue 29665. -/
theorem bounds_15_29665 : exactInterval 15 29665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29665 : oddCount 29665 15 = 9 ∧ acceleratedOrbit 15 29665 = 17821 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29665) = 3 ^ 9 * m + 17821 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29665.1, data_15_29665.2]

/-- Complete interval computation for depth 15, residue 29666. -/
theorem bounds_15_29666 : exactInterval 15 29666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29666 : oddCount 29666 15 = 6 ∧ acceleratedOrbit 15 29666 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29666) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29666.1, data_15_29666.2]

/-- Complete interval computation for depth 15, residue 29667. -/
theorem bounds_15_29667 : exactInterval 15 29667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29667 : oddCount 29667 15 = 6 ∧ acceleratedOrbit 15 29667 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29667) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29667.1, data_15_29667.2]

/-- Complete interval computation for depth 15, residue 29668. -/
theorem bounds_15_29668 : exactInterval 15 29668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29668 : oddCount 29668 15 = 7 ∧ acceleratedOrbit 15 29668 = 1981 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29668) = 3 ^ 7 * m + 1981 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29668.1, data_15_29668.2]

/-- Complete interval computation for depth 15, residue 29669. -/
theorem bounds_15_29669 : exactInterval 15 29669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29669 : oddCount 29669 15 = 7 ∧ acceleratedOrbit 15 29669 = 1981 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29669) = 3 ^ 7 * m + 1981 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29669.1, data_15_29669.2]

/-- Complete interval computation for depth 15, residue 29670. -/
theorem bounds_15_29670 : exactInterval 15 29670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29670 : oddCount 29670 15 = 7 ∧ acceleratedOrbit 15 29670 = 1981 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29670) = 3 ^ 7 * m + 1981 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29670.1, data_15_29670.2]

/-- Complete interval computation for depth 15, residue 29671. -/
theorem bounds_15_29671 : exactInterval 15 29671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29671 : oddCount 29671 15 = 8 ∧ acceleratedOrbit 15 29671 = 5942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29671) = 3 ^ 8 * m + 5942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29671.1, data_15_29671.2]

/-- Complete interval computation for depth 15, residue 29672. -/
theorem bounds_15_29672 : exactInterval 15 29672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29672 : oddCount 29672 15 = 7 ∧ acceleratedOrbit 15 29672 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29672) = 3 ^ 7 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29672.1, data_15_29672.2]

/-- Complete interval computation for depth 15, residue 29673. -/
theorem bounds_15_29673 : exactInterval 15 29673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29673 : oddCount 29673 15 = 9 ∧ acceleratedOrbit 15 29673 = 17825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29673) = 3 ^ 9 * m + 17825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29673.1, data_15_29673.2]

/-- Complete interval computation for depth 15, residue 29674. -/
theorem bounds_15_29674 : exactInterval 15 29674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29674 : oddCount 29674 15 = 7 ∧ acceleratedOrbit 15 29674 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29674) = 3 ^ 7 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29674.1, data_15_29674.2]

/-- Complete interval computation for depth 15, residue 29675. -/
theorem bounds_15_29675 : exactInterval 15 29675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29675 : oddCount 29675 15 = 10 ∧ acceleratedOrbit 15 29675 = 53480 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29675) = 3 ^ 10 * m + 53480 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29675.1, data_15_29675.2]

/-- Complete interval computation for depth 15, residue 29676. -/
theorem bounds_15_29676 : exactInterval 15 29676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29676 : oddCount 29676 15 = 9 ∧ acceleratedOrbit 15 29676 = 17830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29676) = 3 ^ 9 * m + 17830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29676.1, data_15_29676.2]

/-- Complete interval computation for depth 15, residue 29677. -/
theorem bounds_15_29677 : exactInterval 15 29677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29677 : oddCount 29677 15 = 9 ∧ acceleratedOrbit 15 29677 = 17830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29677) = 3 ^ 9 * m + 17830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29677.1, data_15_29677.2]

/-- Complete interval computation for depth 15, residue 29678. -/
theorem bounds_15_29678 : exactInterval 15 29678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29678 : oddCount 29678 15 = 9 ∧ acceleratedOrbit 15 29678 = 17830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29678) = 3 ^ 9 * m + 17830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29678.1, data_15_29678.2]

/-- Complete interval computation for depth 15, residue 29679. -/
theorem bounds_15_29679 : exactInterval 15 29679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29679 : oddCount 29679 15 = 10 ∧ acceleratedOrbit 15 29679 = 53486 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29679) = 3 ^ 10 * m + 53486 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29679.1, data_15_29679.2]

/-- Complete interval computation for depth 15, residue 29680. -/
theorem bounds_15_29680 : exactInterval 15 29680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29680 : oddCount 29680 15 = 7 ∧ acceleratedOrbit 15 29680 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29680) = 3 ^ 7 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29680.1, data_15_29680.2]

/-- Complete interval computation for depth 15, residue 29681. -/
theorem bounds_15_29681 : exactInterval 15 29681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29681 : oddCount 29681 15 = 7 ∧ acceleratedOrbit 15 29681 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29681) = 3 ^ 7 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29681.1, data_15_29681.2]

/-- Complete interval computation for depth 15, residue 29682. -/
theorem bounds_15_29682 : exactInterval 15 29682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29682 : oddCount 29682 15 = 9 ∧ acceleratedOrbit 15 29682 = 17833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29682) = 3 ^ 9 * m + 17833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29682.1, data_15_29682.2]

/-- Complete interval computation for depth 15, residue 29683. -/
theorem bounds_15_29683 : exactInterval 15 29683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29683 : oddCount 29683 15 = 9 ∧ acceleratedOrbit 15 29683 = 17833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29683) = 3 ^ 9 * m + 17833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29683.1, data_15_29683.2]

/-- Complete interval computation for depth 15, residue 29684. -/
theorem bounds_15_29684 : exactInterval 15 29684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29684 : oddCount 29684 15 = 7 ∧ acceleratedOrbit 15 29684 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29684) = 3 ^ 7 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29684.1, data_15_29684.2]

/-- Complete interval computation for depth 15, residue 29685. -/
theorem bounds_15_29685 : exactInterval 15 29685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29685 : oddCount 29685 15 = 7 ∧ acceleratedOrbit 15 29685 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29685) = 3 ^ 7 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29685.1, data_15_29685.2]

/-- Complete interval computation for depth 15, residue 29686. -/
theorem bounds_15_29686 : exactInterval 15 29686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29686 : oddCount 29686 15 = 7 ∧ acceleratedOrbit 15 29686 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29686) = 3 ^ 7 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29686.1, data_15_29686.2]

end Collatz.Research.PassageAtlas.Batch0906
