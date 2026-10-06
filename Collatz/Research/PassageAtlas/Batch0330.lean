import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0330

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10780. -/
theorem bounds_15_10780 : exactInterval 15 10780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10780 : oddCount 10780 15 = 5 ∧ acceleratedOrbit 15 10780 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10780) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10780.1, data_15_10780.2]

/-- Complete interval computation for depth 15, residue 10781. -/
theorem bounds_15_10781 : exactInterval 15 10781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10781 : oddCount 10781 15 = 5 ∧ acceleratedOrbit 15 10781 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10781) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10781.1, data_15_10781.2]

/-- Complete interval computation for depth 15, residue 10782. -/
theorem bounds_15_10782 : exactInterval 15 10782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10782 : oddCount 10782 15 = 5 ∧ acceleratedOrbit 15 10782 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10782) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10782.1, data_15_10782.2]

/-- Complete interval computation for depth 15, residue 10783. -/
theorem bounds_15_10783 : exactInterval 15 10783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10783 : oddCount 10783 15 = 9 ∧ acceleratedOrbit 15 10783 = 6479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10783) = 3 ^ 9 * m + 6479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10783.1, data_15_10783.2]

/-- Complete interval computation for depth 15, residue 10784. -/
theorem bounds_15_10784 : exactInterval 15 10784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10784 : oddCount 10784 15 = 7 ∧ acceleratedOrbit 15 10784 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10784) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10784.1, data_15_10784.2]

/-- Complete interval computation for depth 15, residue 10785. -/
theorem bounds_15_10785 : exactInterval 15 10785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10785 : oddCount 10785 15 = 5 ∧ acceleratedOrbit 15 10785 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10785) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10785.1, data_15_10785.2]

/-- Complete interval computation for depth 15, residue 10786. -/
theorem bounds_15_10786 : exactInterval 15 10786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10786 : oddCount 10786 15 = 7 ∧ acceleratedOrbit 15 10786 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10786) = 3 ^ 7 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10786.1, data_15_10786.2]

/-- Complete interval computation for depth 15, residue 10787. -/
theorem bounds_15_10787 : exactInterval 15 10787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10787 : oddCount 10787 15 = 7 ∧ acceleratedOrbit 15 10787 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10787) = 3 ^ 7 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10787.1, data_15_10787.2]

/-- Complete interval computation for depth 15, residue 10788. -/
theorem bounds_15_10788 : exactInterval 15 10788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10788 : oddCount 10788 15 = 8 ∧ acceleratedOrbit 15 10788 = 2162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10788) = 3 ^ 8 * m + 2162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10788.1, data_15_10788.2]

/-- Complete interval computation for depth 15, residue 10789. -/
theorem bounds_15_10789 : exactInterval 15 10789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10789 : oddCount 10789 15 = 8 ∧ acceleratedOrbit 15 10789 = 2162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10789) = 3 ^ 8 * m + 2162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10789.1, data_15_10789.2]

/-- Complete interval computation for depth 15, residue 10790. -/
theorem bounds_15_10790 : exactInterval 15 10790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10790 : oddCount 10790 15 = 8 ∧ acceleratedOrbit 15 10790 = 2162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10790) = 3 ^ 8 * m + 2162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10790.1, data_15_10790.2]

/-- Complete interval computation for depth 15, residue 10791. -/
theorem bounds_15_10791 : exactInterval 15 10791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10791 : oddCount 10791 15 = 8 ∧ acceleratedOrbit 15 10791 = 2162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10791) = 3 ^ 8 * m + 2162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10791.1, data_15_10791.2]

/-- Complete interval computation for depth 15, residue 10792. -/
theorem bounds_15_10792 : exactInterval 15 10792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10792 : oddCount 10792 15 = 7 ∧ acceleratedOrbit 15 10792 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10792) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10792.1, data_15_10792.2]

/-- Complete interval computation for depth 15, residue 10793. -/
theorem bounds_15_10793 : exactInterval 15 10793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10793 : oddCount 10793 15 = 10 ∧ acceleratedOrbit 15 10793 = 19453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10793) = 3 ^ 10 * m + 19453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10793.1, data_15_10793.2]

/-- Complete interval computation for depth 15, residue 10794. -/
theorem bounds_15_10794 : exactInterval 15 10794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10794 : oddCount 10794 15 = 7 ∧ acceleratedOrbit 15 10794 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10794) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10794.1, data_15_10794.2]

/-- Complete interval computation for depth 15, residue 10795. -/
theorem bounds_15_10795 : exactInterval 15 10795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10795 : oddCount 10795 15 = 7 ∧ acceleratedOrbit 15 10795 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10795) = 3 ^ 7 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10795.1, data_15_10795.2]

/-- Complete interval computation for depth 15, residue 10796. -/
theorem bounds_15_10796 : exactInterval 15 10796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10796 : oddCount 10796 15 = 7 ∧ acceleratedOrbit 15 10796 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10796) = 3 ^ 7 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10796.1, data_15_10796.2]

/-- Complete interval computation for depth 15, residue 10797. -/
theorem bounds_15_10797 : exactInterval 15 10797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10797 : oddCount 10797 15 = 7 ∧ acceleratedOrbit 15 10797 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10797) = 3 ^ 7 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10797.1, data_15_10797.2]

/-- Complete interval computation for depth 15, residue 10798. -/
theorem bounds_15_10798 : exactInterval 15 10798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10798 : oddCount 10798 15 = 7 ∧ acceleratedOrbit 15 10798 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10798) = 3 ^ 7 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10798.1, data_15_10798.2]

/-- Complete interval computation for depth 15, residue 10799. -/
theorem bounds_15_10799 : exactInterval 15 10799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10799 : oddCount 10799 15 = 9 ∧ acceleratedOrbit 15 10799 = 6488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10799) = 3 ^ 9 * m + 6488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10799.1, data_15_10799.2]

/-- Complete interval computation for depth 15, residue 10800. -/
theorem bounds_15_10800 : exactInterval 15 10800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10800 : oddCount 10800 15 = 7 ∧ acceleratedOrbit 15 10800 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10800) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10800.1, data_15_10800.2]

/-- Complete interval computation for depth 15, residue 10801. -/
theorem bounds_15_10801 : exactInterval 15 10801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10801 : oddCount 10801 15 = 9 ∧ acceleratedOrbit 15 10801 = 6493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10801) = 3 ^ 9 * m + 6493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10801.1, data_15_10801.2]

/-- Complete interval computation for depth 15, residue 10802. -/
theorem bounds_15_10802 : exactInterval 15 10802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10802 : oddCount 10802 15 = 9 ∧ acceleratedOrbit 15 10802 = 6493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10802) = 3 ^ 9 * m + 6493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10802.1, data_15_10802.2]

/-- Complete interval computation for depth 15, residue 10803. -/
theorem bounds_15_10803 : exactInterval 15 10803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10803 : oddCount 10803 15 = 9 ∧ acceleratedOrbit 15 10803 = 6493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10803) = 3 ^ 9 * m + 6493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10803.1, data_15_10803.2]

/-- Complete interval computation for depth 15, residue 10804. -/
theorem bounds_15_10804 : exactInterval 15 10804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10804 : oddCount 10804 15 = 7 ∧ acceleratedOrbit 15 10804 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10804) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10804.1, data_15_10804.2]

/-- Complete interval computation for depth 15, residue 10805. -/
theorem bounds_15_10805 : exactInterval 15 10805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10805 : oddCount 10805 15 = 7 ∧ acceleratedOrbit 15 10805 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10805) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10805.1, data_15_10805.2]

/-- Complete interval computation for depth 15, residue 10806. -/
theorem bounds_15_10806 : exactInterval 15 10806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10806 : oddCount 10806 15 = 10 ∧ acceleratedOrbit 15 10806 = 19478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10806) = 3 ^ 10 * m + 19478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10806.1, data_15_10806.2]

/-- Complete interval computation for depth 15, residue 10807. -/
theorem bounds_15_10807 : exactInterval 15 10807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10807 : oddCount 10807 15 = 10 ∧ acceleratedOrbit 15 10807 = 19478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10807) = 3 ^ 10 * m + 19478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10807.1, data_15_10807.2]

/-- Complete interval computation for depth 15, residue 10808. -/
theorem bounds_15_10808 : exactInterval 15 10808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10808 : oddCount 10808 15 = 9 ∧ acceleratedOrbit 15 10808 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10808) = 3 ^ 9 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10808.1, data_15_10808.2]

/-- Complete interval computation for depth 15, residue 10809. -/
theorem bounds_15_10809 : exactInterval 15 10809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10809 : oddCount 10809 15 = 8 ∧ acceleratedOrbit 15 10809 = 2165 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10809) = 3 ^ 8 * m + 2165 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10809.1, data_15_10809.2]

/-- Complete interval computation for depth 15, residue 10810. -/
theorem bounds_15_10810 : exactInterval 15 10810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10810 : oddCount 10810 15 = 9 ∧ acceleratedOrbit 15 10810 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10810) = 3 ^ 9 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10810.1, data_15_10810.2]

/-- Complete interval computation for depth 15, residue 10811. -/
theorem bounds_15_10811 : exactInterval 15 10811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10811 : oddCount 10811 15 = 7 ∧ acceleratedOrbit 15 10811 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10811) = 3 ^ 7 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10811.1, data_15_10811.2]

/-- Complete interval computation for depth 15, residue 10812. -/
theorem bounds_15_10812 : exactInterval 15 10812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10812 : oddCount 10812 15 = 9 ∧ acceleratedOrbit 15 10812 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10812) = 3 ^ 9 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10812.1, data_15_10812.2]

end Collatz.Research.PassageAtlas.Batch0330
