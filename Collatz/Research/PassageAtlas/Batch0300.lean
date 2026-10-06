import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0300

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9797. -/
theorem bounds_15_9797 : exactInterval 15 9797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9797 : oddCount 9797 15 = 5 ∧ acceleratedOrbit 15 9797 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9797) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9797.1, data_15_9797.2]

/-- Complete interval computation for depth 15, residue 9798. -/
theorem bounds_15_9798 : exactInterval 15 9798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9798 : oddCount 9798 15 = 5 ∧ acceleratedOrbit 15 9798 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9798) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9798.1, data_15_9798.2]

/-- Complete interval computation for depth 15, residue 9799. -/
theorem bounds_15_9799 : exactInterval 15 9799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9799 : oddCount 9799 15 = 9 ∧ acceleratedOrbit 15 9799 = 5888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9799) = 3 ^ 9 * m + 5888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9799.1, data_15_9799.2]

/-- Complete interval computation for depth 15, residue 9800. -/
theorem bounds_15_9800 : exactInterval 15 9800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9800 : oddCount 9800 15 = 5 ∧ acceleratedOrbit 15 9800 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9800) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9800.1, data_15_9800.2]

/-- Complete interval computation for depth 15, residue 9801. -/
theorem bounds_15_9801 : exactInterval 15 9801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9801 : oddCount 9801 15 = 8 ∧ acceleratedOrbit 15 9801 = 1963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9801) = 3 ^ 8 * m + 1963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9801.1, data_15_9801.2]

/-- Complete interval computation for depth 15, residue 9802. -/
theorem bounds_15_9802 : exactInterval 15 9802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9802 : oddCount 9802 15 = 5 ∧ acceleratedOrbit 15 9802 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9802) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9802.1, data_15_9802.2]

/-- Complete interval computation for depth 15, residue 9803. -/
theorem bounds_15_9803 : exactInterval 15 9803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9803 : oddCount 9803 15 = 5 ∧ acceleratedOrbit 15 9803 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9803) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9803.1, data_15_9803.2]

/-- Complete interval computation for depth 15, residue 9804. -/
theorem bounds_15_9804 : exactInterval 15 9804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9804 : oddCount 9804 15 = 5 ∧ acceleratedOrbit 15 9804 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9804) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9804.1, data_15_9804.2]

/-- Complete interval computation for depth 15, residue 9805. -/
theorem bounds_15_9805 : exactInterval 15 9805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9805 : oddCount 9805 15 = 5 ∧ acceleratedOrbit 15 9805 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9805) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9805.1, data_15_9805.2]

/-- Complete interval computation for depth 15, residue 9806. -/
theorem bounds_15_9806 : exactInterval 15 9806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9806 : oddCount 9806 15 = 10 ∧ acceleratedOrbit 15 9806 = 17678 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9806) = 3 ^ 10 * m + 17678 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9806.1, data_15_9806.2]

/-- Complete interval computation for depth 15, residue 9807. -/
theorem bounds_15_9807 : exactInterval 15 9807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9807 : oddCount 9807 15 = 10 ∧ acceleratedOrbit 15 9807 = 17678 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9807) = 3 ^ 10 * m + 17678 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9807.1, data_15_9807.2]

/-- Complete interval computation for depth 15, residue 9808. -/
theorem bounds_15_9808 : exactInterval 15 9808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9808 : oddCount 9808 15 = 5 ∧ acceleratedOrbit 15 9808 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9808) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9808.1, data_15_9808.2]

/-- Complete interval computation for depth 15, residue 9809. -/
theorem bounds_15_9809 : exactInterval 15 9809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9809 : oddCount 9809 15 = 7 ∧ acceleratedOrbit 15 9809 = 655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9809) = 3 ^ 7 * m + 655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9809.1, data_15_9809.2]

/-- Complete interval computation for depth 15, residue 9810. -/
theorem bounds_15_9810 : exactInterval 15 9810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9810 : oddCount 9810 15 = 7 ∧ acceleratedOrbit 15 9810 = 655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9810) = 3 ^ 7 * m + 655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9810.1, data_15_9810.2]

/-- Complete interval computation for depth 15, residue 9811. -/
theorem bounds_15_9811 : exactInterval 15 9811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9811 : oddCount 9811 15 = 7 ∧ acceleratedOrbit 15 9811 = 655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9811) = 3 ^ 7 * m + 655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9811.1, data_15_9811.2]

/-- Complete interval computation for depth 15, residue 9812. -/
theorem bounds_15_9812 : exactInterval 15 9812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9812 : oddCount 9812 15 = 5 ∧ acceleratedOrbit 15 9812 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9812) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9812.1, data_15_9812.2]

/-- Complete interval computation for depth 15, residue 9813. -/
theorem bounds_15_9813 : exactInterval 15 9813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9813 : oddCount 9813 15 = 5 ∧ acceleratedOrbit 15 9813 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9813) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9813.1, data_15_9813.2]

/-- Complete interval computation for depth 15, residue 9814. -/
theorem bounds_15_9814 : exactInterval 15 9814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9814 : oddCount 9814 15 = 7 ∧ acceleratedOrbit 15 9814 = 656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9814) = 3 ^ 7 * m + 656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9814.1, data_15_9814.2]

/-- Complete interval computation for depth 15, residue 9815. -/
theorem bounds_15_9815 : exactInterval 15 9815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9815 : oddCount 9815 15 = 7 ∧ acceleratedOrbit 15 9815 = 656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9815) = 3 ^ 7 * m + 656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9815.1, data_15_9815.2]

/-- Complete interval computation for depth 15, residue 9816. -/
theorem bounds_15_9816 : exactInterval 15 9816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9816 : oddCount 9816 15 = 5 ∧ acceleratedOrbit 15 9816 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9816) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9816.1, data_15_9816.2]

/-- Complete interval computation for depth 15, residue 9817. -/
theorem bounds_15_9817 : exactInterval 15 9817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9817 : oddCount 9817 15 = 7 ∧ acceleratedOrbit 15 9817 = 656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9817) = 3 ^ 7 * m + 656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9817.1, data_15_9817.2]

/-- Complete interval computation for depth 15, residue 9818. -/
theorem bounds_15_9818 : exactInterval 15 9818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9818 : oddCount 9818 15 = 5 ∧ acceleratedOrbit 15 9818 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9818) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9818.1, data_15_9818.2]

/-- Complete interval computation for depth 15, residue 9819. -/
theorem bounds_15_9819 : exactInterval 15 9819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9819 : oddCount 9819 15 = 10 ∧ acceleratedOrbit 15 9819 = 17698 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9819) = 3 ^ 10 * m + 17698 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9819.1, data_15_9819.2]

/-- Complete interval computation for depth 15, residue 9820. -/
theorem bounds_15_9820 : exactInterval 15 9820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9820 : oddCount 9820 15 = 5 ∧ acceleratedOrbit 15 9820 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9820) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9820.1, data_15_9820.2]

/-- Complete interval computation for depth 15, residue 9821. -/
theorem bounds_15_9821 : exactInterval 15 9821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9821 : oddCount 9821 15 = 5 ∧ acceleratedOrbit 15 9821 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9821) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9821.1, data_15_9821.2]

/-- Complete interval computation for depth 15, residue 9822. -/
theorem bounds_15_9822 : exactInterval 15 9822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9822 : oddCount 9822 15 = 9 ∧ acceleratedOrbit 15 9822 = 5903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9822) = 3 ^ 9 * m + 5903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9822.1, data_15_9822.2]

/-- Complete interval computation for depth 15, residue 9823. -/
theorem bounds_15_9823 : exactInterval 15 9823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9823 : oddCount 9823 15 = 9 ∧ acceleratedOrbit 15 9823 = 5903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9823) = 3 ^ 9 * m + 5903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9823.1, data_15_9823.2]

/-- Complete interval computation for depth 15, residue 9824. -/
theorem bounds_15_9824 : exactInterval 15 9824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9824 : oddCount 9824 15 = 5 ∧ acceleratedOrbit 15 9824 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9824) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9824.1, data_15_9824.2]

/-- Complete interval computation for depth 15, residue 9825. -/
theorem bounds_15_9825 : exactInterval 15 9825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9825 : oddCount 9825 15 = 8 ∧ acceleratedOrbit 15 9825 = 1970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9825) = 3 ^ 8 * m + 1970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9825.1, data_15_9825.2]

/-- Complete interval computation for depth 15, residue 9826. -/
theorem bounds_15_9826 : exactInterval 15 9826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9826 : oddCount 9826 15 = 5 ∧ acceleratedOrbit 15 9826 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9826) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9826.1, data_15_9826.2]

/-- Complete interval computation for depth 15, residue 9827. -/
theorem bounds_15_9827 : exactInterval 15 9827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9827 : oddCount 9827 15 = 5 ∧ acceleratedOrbit 15 9827 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9827) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9827.1, data_15_9827.2]

/-- Complete interval computation for depth 15, residue 9828. -/
theorem bounds_15_9828 : exactInterval 15 9828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9828 : oddCount 9828 15 = 5 ∧ acceleratedOrbit 15 9828 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9828) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9828.1, data_15_9828.2]

/-- Complete interval computation for depth 15, residue 9829. -/
theorem bounds_15_9829 : exactInterval 15 9829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9829 : oddCount 9829 15 = 5 ∧ acceleratedOrbit 15 9829 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9829) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9829.1, data_15_9829.2]

end Collatz.Research.PassageAtlas.Batch0300
