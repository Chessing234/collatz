import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0301

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9830. -/
theorem bounds_15_9830 : exactInterval 15 9830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9830 : oddCount 9830 15 = 5 ∧ acceleratedOrbit 15 9830 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9830) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9830.1, data_15_9830.2]

/-- Complete interval computation for depth 15, residue 9831. -/
theorem bounds_15_9831 : exactInterval 15 9831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9831 : oddCount 9831 15 = 11 ∧ acceleratedOrbit 15 9831 = 53156 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9831) = 3 ^ 11 * m + 53156 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9831.1, data_15_9831.2]

/-- Complete interval computation for depth 15, residue 9832. -/
theorem bounds_15_9832 : exactInterval 15 9832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9832 : oddCount 9832 15 = 5 ∧ acceleratedOrbit 15 9832 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9832) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9832.1, data_15_9832.2]

/-- Complete interval computation for depth 15, residue 9833. -/
theorem bounds_15_9833 : exactInterval 15 9833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9833 : oddCount 9833 15 = 9 ∧ acceleratedOrbit 15 9833 = 5908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9833) = 3 ^ 9 * m + 5908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9833.1, data_15_9833.2]

/-- Complete interval computation for depth 15, residue 9834. -/
theorem bounds_15_9834 : exactInterval 15 9834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9834 : oddCount 9834 15 = 5 ∧ acceleratedOrbit 15 9834 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9834) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9834.1, data_15_9834.2]

/-- Complete interval computation for depth 15, residue 9835. -/
theorem bounds_15_9835 : exactInterval 15 9835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9835 : oddCount 9835 15 = 10 ∧ acceleratedOrbit 15 9835 = 17729 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9835) = 3 ^ 10 * m + 17729 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9835.1, data_15_9835.2]

/-- Complete interval computation for depth 15, residue 9836. -/
theorem bounds_15_9836 : exactInterval 15 9836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9836 : oddCount 9836 15 = 10 ∧ acceleratedOrbit 15 9836 = 17738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9836) = 3 ^ 10 * m + 17738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9836.1, data_15_9836.2]

/-- Complete interval computation for depth 15, residue 9837. -/
theorem bounds_15_9837 : exactInterval 15 9837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9837 : oddCount 9837 15 = 10 ∧ acceleratedOrbit 15 9837 = 17738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9837) = 3 ^ 10 * m + 17738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9837.1, data_15_9837.2]

/-- Complete interval computation for depth 15, residue 9838. -/
theorem bounds_15_9838 : exactInterval 15 9838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9838 : oddCount 9838 15 = 10 ∧ acceleratedOrbit 15 9838 = 17738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9838) = 3 ^ 10 * m + 17738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9838.1, data_15_9838.2]

/-- Complete interval computation for depth 15, residue 9839. -/
theorem bounds_15_9839 : exactInterval 15 9839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9839 : oddCount 9839 15 = 9 ∧ acceleratedOrbit 15 9839 = 5912 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9839) = 3 ^ 9 * m + 5912 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9839.1, data_15_9839.2]

/-- Complete interval computation for depth 15, residue 9840. -/
theorem bounds_15_9840 : exactInterval 15 9840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9840 : oddCount 9840 15 = 7 ∧ acceleratedOrbit 15 9840 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9840) = 3 ^ 7 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9840.1, data_15_9840.2]

/-- Complete interval computation for depth 15, residue 9841. -/
theorem bounds_15_9841 : exactInterval 15 9841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9841 : oddCount 9841 15 = 5 ∧ acceleratedOrbit 15 9841 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9841) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9841.1, data_15_9841.2]

/-- Complete interval computation for depth 15, residue 9842. -/
theorem bounds_15_9842 : exactInterval 15 9842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9842 : oddCount 9842 15 = 8 ∧ acceleratedOrbit 15 9842 = 1972 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9842) = 3 ^ 8 * m + 1972 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9842.1, data_15_9842.2]

/-- Complete interval computation for depth 15, residue 9843. -/
theorem bounds_15_9843 : exactInterval 15 9843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9843 : oddCount 9843 15 = 8 ∧ acceleratedOrbit 15 9843 = 1972 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9843) = 3 ^ 8 * m + 1972 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9843.1, data_15_9843.2]

/-- Complete interval computation for depth 15, residue 9844. -/
theorem bounds_15_9844 : exactInterval 15 9844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9844 : oddCount 9844 15 = 7 ∧ acceleratedOrbit 15 9844 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9844) = 3 ^ 7 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9844.1, data_15_9844.2]

/-- Complete interval computation for depth 15, residue 9845. -/
theorem bounds_15_9845 : exactInterval 15 9845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9845 : oddCount 9845 15 = 7 ∧ acceleratedOrbit 15 9845 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9845) = 3 ^ 7 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9845.1, data_15_9845.2]

/-- Complete interval computation for depth 15, residue 9846. -/
theorem bounds_15_9846 : exactInterval 15 9846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9846 : oddCount 9846 15 = 7 ∧ acceleratedOrbit 15 9846 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9846) = 3 ^ 7 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9846.1, data_15_9846.2]

/-- Complete interval computation for depth 15, residue 9847. -/
theorem bounds_15_9847 : exactInterval 15 9847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9847 : oddCount 9847 15 = 7 ∧ acceleratedOrbit 15 9847 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9847) = 3 ^ 7 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9847.1, data_15_9847.2]

/-- Complete interval computation for depth 15, residue 9848. -/
theorem bounds_15_9848 : exactInterval 15 9848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9848 : oddCount 9848 15 = 7 ∧ acceleratedOrbit 15 9848 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9848) = 3 ^ 7 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9848.1, data_15_9848.2]

/-- Complete interval computation for depth 15, residue 9849. -/
theorem bounds_15_9849 : exactInterval 15 9849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9849 : oddCount 9849 15 = 8 ∧ acceleratedOrbit 15 9849 = 1973 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9849) = 3 ^ 8 * m + 1973 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9849.1, data_15_9849.2]

/-- Complete interval computation for depth 15, residue 9850. -/
theorem bounds_15_9850 : exactInterval 15 9850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9850 : oddCount 9850 15 = 7 ∧ acceleratedOrbit 15 9850 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9850) = 3 ^ 7 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9850.1, data_15_9850.2]

/-- Complete interval computation for depth 15, residue 9851. -/
theorem bounds_15_9851 : exactInterval 15 9851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9851 : oddCount 9851 15 = 7 ∧ acceleratedOrbit 15 9851 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9851) = 3 ^ 7 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9851.1, data_15_9851.2]

/-- Complete interval computation for depth 15, residue 9852. -/
theorem bounds_15_9852 : exactInterval 15 9852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9852 : oddCount 9852 15 = 9 ∧ acceleratedOrbit 15 9852 = 5921 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9852) = 3 ^ 9 * m + 5921 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9852.1, data_15_9852.2]

/-- Complete interval computation for depth 15, residue 9853. -/
theorem bounds_15_9853 : exactInterval 15 9853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9853 : oddCount 9853 15 = 9 ∧ acceleratedOrbit 15 9853 = 5921 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9853) = 3 ^ 9 * m + 5921 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9853.1, data_15_9853.2]

/-- Complete interval computation for depth 15, residue 9854. -/
theorem bounds_15_9854 : exactInterval 15 9854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9854 : oddCount 9854 15 = 9 ∧ acceleratedOrbit 15 9854 = 5921 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9854) = 3 ^ 9 * m + 5921 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9854.1, data_15_9854.2]

/-- Complete interval computation for depth 15, residue 9855. -/
theorem bounds_15_9855 : exactInterval 15 9855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9855 : oddCount 9855 15 = 13 ∧ acceleratedOrbit 15 9855 = 479546 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9855) = 3 ^ 13 * m + 479546 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9855.1, data_15_9855.2]

/-- Complete interval computation for depth 15, residue 9856. -/
theorem bounds_15_9856 : exactInterval 15 9856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9856 : oddCount 9856 15 = 4 ∧ acceleratedOrbit 15 9856 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9856) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9856.1, data_15_9856.2]

/-- Complete interval computation for depth 15, residue 9857. -/
theorem bounds_15_9857 : exactInterval 15 9857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9857 : oddCount 9857 15 = 9 ∧ acceleratedOrbit 15 9857 = 5923 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9857) = 3 ^ 9 * m + 5923 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9857.1, data_15_9857.2]

/-- Complete interval computation for depth 15, residue 9858. -/
theorem bounds_15_9858 : exactInterval 15 9858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9858 : oddCount 9858 15 = 5 ∧ acceleratedOrbit 15 9858 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9858) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9858.1, data_15_9858.2]

/-- Complete interval computation for depth 15, residue 9859. -/
theorem bounds_15_9859 : exactInterval 15 9859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9859 : oddCount 9859 15 = 5 ∧ acceleratedOrbit 15 9859 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9859) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9859.1, data_15_9859.2]

/-- Complete interval computation for depth 15, residue 9860. -/
theorem bounds_15_9860 : exactInterval 15 9860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9860 : oddCount 9860 15 = 7 ∧ acceleratedOrbit 15 9860 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9860) = 3 ^ 7 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9860.1, data_15_9860.2]

/-- Complete interval computation for depth 15, residue 9861. -/
theorem bounds_15_9861 : exactInterval 15 9861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9861 : oddCount 9861 15 = 7 ∧ acceleratedOrbit 15 9861 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9861) = 3 ^ 7 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9861.1, data_15_9861.2]

/-- Complete interval computation for depth 15, residue 9862. -/
theorem bounds_15_9862 : exactInterval 15 9862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9862 : oddCount 9862 15 = 7 ∧ acceleratedOrbit 15 9862 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9862) = 3 ^ 7 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9862.1, data_15_9862.2]

end Collatz.Research.PassageAtlas.Batch0301
