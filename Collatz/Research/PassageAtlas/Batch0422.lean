import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0422

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13795. -/
theorem bounds_15_13795 : exactInterval 15 13795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13795 : oddCount 13795 15 = 5 ∧ acceleratedOrbit 15 13795 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13795) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13795.1, data_15_13795.2]

/-- Complete interval computation for depth 15, residue 13796. -/
theorem bounds_15_13796 : exactInterval 15 13796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13796 : oddCount 13796 15 = 8 ∧ acceleratedOrbit 15 13796 = 2764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13796) = 3 ^ 8 * m + 2764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13796.1, data_15_13796.2]

/-- Complete interval computation for depth 15, residue 13797. -/
theorem bounds_15_13797 : exactInterval 15 13797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13797 : oddCount 13797 15 = 8 ∧ acceleratedOrbit 15 13797 = 2764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13797) = 3 ^ 8 * m + 2764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13797.1, data_15_13797.2]

/-- Complete interval computation for depth 15, residue 13798. -/
theorem bounds_15_13798 : exactInterval 15 13798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13798 : oddCount 13798 15 = 8 ∧ acceleratedOrbit 15 13798 = 2764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13798) = 3 ^ 8 * m + 2764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13798.1, data_15_13798.2]

/-- Complete interval computation for depth 15, residue 13799. -/
theorem bounds_15_13799 : exactInterval 15 13799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13799 : oddCount 13799 15 = 9 ∧ acceleratedOrbit 15 13799 = 8290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13799) = 3 ^ 9 * m + 8290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13799.1, data_15_13799.2]

/-- Complete interval computation for depth 15, residue 13800. -/
theorem bounds_15_13800 : exactInterval 15 13800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13800 : oddCount 13800 15 = 6 ∧ acceleratedOrbit 15 13800 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13800) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13800.1, data_15_13800.2]

/-- Complete interval computation for depth 15, residue 13801. -/
theorem bounds_15_13801 : exactInterval 15 13801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13801 : oddCount 13801 15 = 11 ∧ acceleratedOrbit 15 13801 = 74621 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13801) = 3 ^ 11 * m + 74621 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13801.1, data_15_13801.2]

/-- Complete interval computation for depth 15, residue 13802. -/
theorem bounds_15_13802 : exactInterval 15 13802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13802 : oddCount 13802 15 = 6 ∧ acceleratedOrbit 15 13802 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13802) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13802.1, data_15_13802.2]

/-- Complete interval computation for depth 15, residue 13803. -/
theorem bounds_15_13803 : exactInterval 15 13803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13803 : oddCount 13803 15 = 10 ∧ acceleratedOrbit 15 13803 = 24877 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13803) = 3 ^ 10 * m + 24877 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13803.1, data_15_13803.2]

/-- Complete interval computation for depth 15, residue 13804. -/
theorem bounds_15_13804 : exactInterval 15 13804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13804 : oddCount 13804 15 = 7 ∧ acceleratedOrbit 15 13804 = 922 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13804) = 3 ^ 7 * m + 922 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13804.1, data_15_13804.2]

/-- Complete interval computation for depth 15, residue 13805. -/
theorem bounds_15_13805 : exactInterval 15 13805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13805 : oddCount 13805 15 = 7 ∧ acceleratedOrbit 15 13805 = 922 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13805) = 3 ^ 7 * m + 922 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13805.1, data_15_13805.2]

/-- Complete interval computation for depth 15, residue 13806. -/
theorem bounds_15_13806 : exactInterval 15 13806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13806 : oddCount 13806 15 = 7 ∧ acceleratedOrbit 15 13806 = 922 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13806) = 3 ^ 7 * m + 922 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13806.1, data_15_13806.2]

/-- Complete interval computation for depth 15, residue 13807. -/
theorem bounds_15_13807 : exactInterval 15 13807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13807 : oddCount 13807 15 = 10 ∧ acceleratedOrbit 15 13807 = 24884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13807) = 3 ^ 10 * m + 24884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13807.1, data_15_13807.2]

/-- Complete interval computation for depth 15, residue 13808. -/
theorem bounds_15_13808 : exactInterval 15 13808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13808 : oddCount 13808 15 = 6 ∧ acceleratedOrbit 15 13808 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13808) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13808.1, data_15_13808.2]

/-- Complete interval computation for depth 15, residue 13809. -/
theorem bounds_15_13809 : exactInterval 15 13809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13809 : oddCount 13809 15 = 6 ∧ acceleratedOrbit 15 13809 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13809) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13809.1, data_15_13809.2]

/-- Complete interval computation for depth 15, residue 13810. -/
theorem bounds_15_13810 : exactInterval 15 13810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13810 : oddCount 13810 15 = 8 ∧ acceleratedOrbit 15 13810 = 2767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13810) = 3 ^ 8 * m + 2767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13810.1, data_15_13810.2]

/-- Complete interval computation for depth 15, residue 13811. -/
theorem bounds_15_13811 : exactInterval 15 13811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13811 : oddCount 13811 15 = 8 ∧ acceleratedOrbit 15 13811 = 2767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13811) = 3 ^ 8 * m + 2767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13811.1, data_15_13811.2]

/-- Complete interval computation for depth 15, residue 13812. -/
theorem bounds_15_13812 : exactInterval 15 13812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13812 : oddCount 13812 15 = 6 ∧ acceleratedOrbit 15 13812 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13812) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13812.1, data_15_13812.2]

/-- Complete interval computation for depth 15, residue 13813. -/
theorem bounds_15_13813 : exactInterval 15 13813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13813 : oddCount 13813 15 = 6 ∧ acceleratedOrbit 15 13813 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13813) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13813.1, data_15_13813.2]

/-- Complete interval computation for depth 15, residue 13814. -/
theorem bounds_15_13814 : exactInterval 15 13814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13814 : oddCount 13814 15 = 9 ∧ acceleratedOrbit 15 13814 = 8300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13814) = 3 ^ 9 * m + 8300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13814.1, data_15_13814.2]

/-- Complete interval computation for depth 15, residue 13815. -/
theorem bounds_15_13815 : exactInterval 15 13815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13815 : oddCount 13815 15 = 9 ∧ acceleratedOrbit 15 13815 = 8300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13815) = 3 ^ 9 * m + 8300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13815.1, data_15_13815.2]

/-- Complete interval computation for depth 15, residue 13816. -/
theorem bounds_15_13816 : exactInterval 15 13816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13816 : oddCount 13816 15 = 8 ∧ acceleratedOrbit 15 13816 = 2768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13816) = 3 ^ 8 * m + 2768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13816.1, data_15_13816.2]

/-- Complete interval computation for depth 15, residue 13817. -/
theorem bounds_15_13817 : exactInterval 15 13817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13817 : oddCount 13817 15 = 9 ∧ acceleratedOrbit 15 13817 = 8302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13817) = 3 ^ 9 * m + 8302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13817.1, data_15_13817.2]

/-- Complete interval computation for depth 15, residue 13818. -/
theorem bounds_15_13818 : exactInterval 15 13818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13818 : oddCount 13818 15 = 8 ∧ acceleratedOrbit 15 13818 = 2768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13818) = 3 ^ 8 * m + 2768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13818.1, data_15_13818.2]

/-- Complete interval computation for depth 15, residue 13819. -/
theorem bounds_15_13819 : exactInterval 15 13819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13819 : oddCount 13819 15 = 10 ∧ acceleratedOrbit 15 13819 = 24907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13819) = 3 ^ 10 * m + 24907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13819.1, data_15_13819.2]

/-- Complete interval computation for depth 15, residue 13820. -/
theorem bounds_15_13820 : exactInterval 15 13820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13820 : oddCount 13820 15 = 8 ∧ acceleratedOrbit 15 13820 = 2768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13820) = 3 ^ 8 * m + 2768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13820.1, data_15_13820.2]

/-- Complete interval computation for depth 15, residue 13821. -/
theorem bounds_15_13821 : exactInterval 15 13821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13821 : oddCount 13821 15 = 8 ∧ acceleratedOrbit 15 13821 = 2768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13821) = 3 ^ 8 * m + 2768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13821.1, data_15_13821.2]

/-- Complete interval computation for depth 15, residue 13822. -/
theorem bounds_15_13822 : exactInterval 15 13822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13822 : oddCount 13822 15 = 11 ∧ acceleratedOrbit 15 13822 = 74735 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13822) = 3 ^ 11 * m + 74735 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13822.1, data_15_13822.2]

/-- Complete interval computation for depth 15, residue 13823. -/
theorem bounds_15_13823 : exactInterval 15 13823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13823 : oddCount 13823 15 = 11 ∧ acceleratedOrbit 15 13823 = 74735 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13823) = 3 ^ 11 * m + 74735 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13823.1, data_15_13823.2]

/-- Complete interval computation for depth 15, residue 13824. -/
theorem bounds_15_13824 : exactInterval 15 13824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13824 : oddCount 13824 15 = 5 ∧ acceleratedOrbit 15 13824 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13824) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13824.1, data_15_13824.2]

/-- Complete interval computation for depth 15, residue 13825. -/
theorem bounds_15_13825 : exactInterval 15 13825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13825 : oddCount 13825 15 = 7 ∧ acceleratedOrbit 15 13825 = 923 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13825) = 3 ^ 7 * m + 923 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13825.1, data_15_13825.2]

/-- Complete interval computation for depth 15, residue 13826. -/
theorem bounds_15_13826 : exactInterval 15 13826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13826 : oddCount 13826 15 = 6 ∧ acceleratedOrbit 15 13826 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13826) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13826.1, data_15_13826.2]

/-- Complete interval computation for depth 15, residue 13827. -/
theorem bounds_15_13827 : exactInterval 15 13827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13827 : oddCount 13827 15 = 6 ∧ acceleratedOrbit 15 13827 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13827) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13827.1, data_15_13827.2]

end Collatz.Research.PassageAtlas.Batch0422
