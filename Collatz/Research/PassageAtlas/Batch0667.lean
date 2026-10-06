import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0667

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21823. -/
theorem bounds_15_21823 : exactInterval 15 21823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21823 : oddCount 21823 15 = 10 ∧ acceleratedOrbit 15 21823 = 39329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21823) = 3 ^ 10 * m + 39329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21823.1, data_15_21823.2]

/-- Complete interval computation for depth 15, residue 21824. -/
theorem bounds_15_21824 : exactInterval 15 21824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21824 : oddCount 21824 15 = 1 ∧ acceleratedOrbit 15 21824 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21824) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21824.1, data_15_21824.2]

/-- Complete interval computation for depth 15, residue 21825. -/
theorem bounds_15_21825 : exactInterval 15 21825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21825 : oddCount 21825 15 = 9 ∧ acceleratedOrbit 15 21825 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21825) = 3 ^ 9 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21825.1, data_15_21825.2]

/-- Complete interval computation for depth 15, residue 21826. -/
theorem bounds_15_21826 : exactInterval 15 21826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21826 : oddCount 21826 15 = 9 ∧ acceleratedOrbit 15 21826 = 13115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21826) = 3 ^ 9 * m + 13115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21826.1, data_15_21826.2]

/-- Complete interval computation for depth 15, residue 21827. -/
theorem bounds_15_21827 : exactInterval 15 21827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21827 : oddCount 21827 15 = 9 ∧ acceleratedOrbit 15 21827 = 13115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21827) = 3 ^ 9 * m + 13115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21827.1, data_15_21827.2]

/-- Complete interval computation for depth 15, residue 21828. -/
theorem bounds_15_21828 : exactInterval 15 21828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21828 : oddCount 21828 15 = 10 ∧ acceleratedOrbit 15 21828 = 39365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21828) = 3 ^ 10 * m + 39365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21828.1, data_15_21828.2]

/-- Complete interval computation for depth 15, residue 21829. -/
theorem bounds_15_21829 : exactInterval 15 21829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21829 : oddCount 21829 15 = 10 ∧ acceleratedOrbit 15 21829 = 39365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21829) = 3 ^ 10 * m + 39365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21829.1, data_15_21829.2]

/-- Complete interval computation for depth 15, residue 21830. -/
theorem bounds_15_21830 : exactInterval 15 21830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21830 : oddCount 21830 15 = 10 ∧ acceleratedOrbit 15 21830 = 39365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21830) = 3 ^ 10 * m + 39365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21830.1, data_15_21830.2]

/-- Complete interval computation for depth 15, residue 21831. -/
theorem bounds_15_21831 : exactInterval 15 21831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21831 : oddCount 21831 15 = 11 ∧ acceleratedOrbit 15 21831 = 118030 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21831) = 3 ^ 11 * m + 118030 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21831.1, data_15_21831.2]

/-- Complete interval computation for depth 15, residue 21832. -/
theorem bounds_15_21832 : exactInterval 15 21832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21832 : oddCount 21832 15 = 11 ∧ acceleratedOrbit 15 21832 = 118097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21832) = 3 ^ 11 * m + 118097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21832.1, data_15_21832.2]

/-- Complete interval computation for depth 15, residue 21833. -/
theorem bounds_15_21833 : exactInterval 15 21833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21833 : oddCount 21833 15 = 9 ∧ acceleratedOrbit 15 21833 = 13117 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21833) = 3 ^ 9 * m + 13117 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21833.1, data_15_21833.2]

/-- Complete interval computation for depth 15, residue 21834. -/
theorem bounds_15_21834 : exactInterval 15 21834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21834 : oddCount 21834 15 = 11 ∧ acceleratedOrbit 15 21834 = 118097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21834) = 3 ^ 11 * m + 118097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21834.1, data_15_21834.2]

/-- Complete interval computation for depth 15, residue 21835. -/
theorem bounds_15_21835 : exactInterval 15 21835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21835 : oddCount 21835 15 = 10 ∧ acceleratedOrbit 15 21835 = 39365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21835) = 3 ^ 10 * m + 39365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21835.1, data_15_21835.2]

/-- Complete interval computation for depth 15, residue 21836. -/
theorem bounds_15_21836 : exactInterval 15 21836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21836 : oddCount 21836 15 = 11 ∧ acceleratedOrbit 15 21836 = 118097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21836) = 3 ^ 11 * m + 118097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21836.1, data_15_21836.2]

/-- Complete interval computation for depth 15, residue 21837. -/
theorem bounds_15_21837 : exactInterval 15 21837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21837 : oddCount 21837 15 = 11 ∧ acceleratedOrbit 15 21837 = 118097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21837) = 3 ^ 11 * m + 118097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21837.1, data_15_21837.2]

/-- Complete interval computation for depth 15, residue 21838. -/
theorem bounds_15_21838 : exactInterval 15 21838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21838 : oddCount 21838 15 = 10 ∧ acceleratedOrbit 15 21838 = 39359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21838) = 3 ^ 10 * m + 39359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21838.1, data_15_21838.2]

/-- Complete interval computation for depth 15, residue 21839. -/
theorem bounds_15_21839 : exactInterval 15 21839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21839 : oddCount 21839 15 = 10 ∧ acceleratedOrbit 15 21839 = 39359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21839) = 3 ^ 10 * m + 39359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21839.1, data_15_21839.2]

/-- Complete interval computation for depth 15, residue 21840. -/
theorem bounds_15_21840 : exactInterval 15 21840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21840 : oddCount 21840 15 = 1 ∧ acceleratedOrbit 15 21840 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21840) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21840.1, data_15_21840.2]

/-- Complete interval computation for depth 15, residue 21841. -/
theorem bounds_15_21841 : exactInterval 15 21841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21841 : oddCount 21841 15 = 12 ∧ acceleratedOrbit 15 21841 = 354293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21841) = 3 ^ 12 * m + 354293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21841.1, data_15_21841.2]

/-- Complete interval computation for depth 15, residue 21842. -/
theorem bounds_15_21842 : exactInterval 15 21842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21842 : oddCount 21842 15 = 13 ∧ acceleratedOrbit 15 21842 = 1062881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21842) = 3 ^ 13 * m + 1062881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21842.1, data_15_21842.2]

/-- Complete interval computation for depth 15, residue 21843. -/
theorem bounds_15_21843 : exactInterval 15 21843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21843 : oddCount 21843 15 = 13 ∧ acceleratedOrbit 15 21843 = 1062881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21843) = 3 ^ 13 * m + 1062881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21843.1, data_15_21843.2]

/-- Complete interval computation for depth 15, residue 21844. -/
theorem bounds_15_21844 : exactInterval 15 21844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21844 : oddCount 21844 15 = 1 ∧ acceleratedOrbit 15 21844 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21844) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21844.1, data_15_21844.2]

/-- Complete interval computation for depth 15, residue 21845. -/
theorem bounds_15_21845 : exactInterval 15 21845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21845 : oddCount 21845 15 = 1 ∧ acceleratedOrbit 15 21845 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21845) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21845.1, data_15_21845.2]

/-- Complete interval computation for depth 15, residue 21846. -/
theorem bounds_15_21846 : exactInterval 15 21846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21846 : oddCount 21846 15 = 8 ∧ acceleratedOrbit 15 21846 = 4376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21846) = 3 ^ 8 * m + 4376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21846.1, data_15_21846.2]

/-- Complete interval computation for depth 15, residue 21847. -/
theorem bounds_15_21847 : exactInterval 15 21847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21847 : oddCount 21847 15 = 8 ∧ acceleratedOrbit 15 21847 = 4376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21847) = 3 ^ 8 * m + 4376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21847.1, data_15_21847.2]

/-- Complete interval computation for depth 15, residue 21848. -/
theorem bounds_15_21848 : exactInterval 15 21848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21848 : oddCount 21848 15 = 7 ∧ acceleratedOrbit 15 21848 = 1460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21848) = 3 ^ 7 * m + 1460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21848.1, data_15_21848.2]

/-- Complete interval computation for depth 15, residue 21849. -/
theorem bounds_15_21849 : exactInterval 15 21849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21849 : oddCount 21849 15 = 7 ∧ acceleratedOrbit 15 21849 = 1459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21849) = 3 ^ 7 * m + 1459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21849.1, data_15_21849.2]

/-- Complete interval computation for depth 15, residue 21850. -/
theorem bounds_15_21850 : exactInterval 15 21850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21850 : oddCount 21850 15 = 7 ∧ acceleratedOrbit 15 21850 = 1460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21850) = 3 ^ 7 * m + 1460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21850.1, data_15_21850.2]

/-- Complete interval computation for depth 15, residue 21851. -/
theorem bounds_15_21851 : exactInterval 15 21851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21851 : oddCount 21851 15 = 8 ∧ acceleratedOrbit 15 21851 = 4376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21851) = 3 ^ 8 * m + 4376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21851.1, data_15_21851.2]

/-- Complete interval computation for depth 15, residue 21852. -/
theorem bounds_15_21852 : exactInterval 15 21852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21852 : oddCount 21852 15 = 7 ∧ acceleratedOrbit 15 21852 = 1460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21852) = 3 ^ 7 * m + 1460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21852.1, data_15_21852.2]

/-- Complete interval computation for depth 15, residue 21853. -/
theorem bounds_15_21853 : exactInterval 15 21853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21853 : oddCount 21853 15 = 7 ∧ acceleratedOrbit 15 21853 = 1460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21853) = 3 ^ 7 * m + 1460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21853.1, data_15_21853.2]

/-- Complete interval computation for depth 15, residue 21854. -/
theorem bounds_15_21854 : exactInterval 15 21854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21854 : oddCount 21854 15 = 7 ∧ acceleratedOrbit 15 21854 = 1459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21854) = 3 ^ 7 * m + 1459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21854.1, data_15_21854.2]

/-- Complete interval computation for depth 15, residue 21855. -/
theorem bounds_15_21855 : exactInterval 15 21855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21855 : oddCount 21855 15 = 7 ∧ acceleratedOrbit 15 21855 = 1459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21855) = 3 ^ 7 * m + 1459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21855.1, data_15_21855.2]

end Collatz.Research.PassageAtlas.Batch0667
