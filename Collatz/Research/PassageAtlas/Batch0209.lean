import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0209

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6815. -/
theorem bounds_15_6815 : exactInterval 15 6815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6815 : oddCount 6815 15 = 10 ∧ acceleratedOrbit 15 6815 = 12284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6815) = 3 ^ 10 * m + 12284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6815.1, data_15_6815.2]

/-- Complete interval computation for depth 15, residue 6816. -/
theorem bounds_15_6816 : exactInterval 15 6816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6816 : oddCount 6816 15 = 2 ∧ acceleratedOrbit 15 6816 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6816) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6816.1, data_15_6816.2]

/-- Complete interval computation for depth 15, residue 6817. -/
theorem bounds_15_6817 : exactInterval 15 6817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6817 : oddCount 6817 15 = 9 ∧ acceleratedOrbit 15 6817 = 4097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6817) = 3 ^ 9 * m + 4097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6817.1, data_15_6817.2]

/-- Complete interval computation for depth 15, residue 6818. -/
theorem bounds_15_6818 : exactInterval 15 6818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6818 : oddCount 6818 15 = 10 ∧ acceleratedOrbit 15 6818 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6818) = 3 ^ 10 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6818.1, data_15_6818.2]

/-- Complete interval computation for depth 15, residue 6819. -/
theorem bounds_15_6819 : exactInterval 15 6819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6819 : oddCount 6819 15 = 10 ∧ acceleratedOrbit 15 6819 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6819) = 3 ^ 10 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6819.1, data_15_6819.2]

/-- Complete interval computation for depth 15, residue 6820. -/
theorem bounds_15_6820 : exactInterval 15 6820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6820 : oddCount 6820 15 = 10 ∧ acceleratedOrbit 15 6820 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6820) = 3 ^ 10 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6820.1, data_15_6820.2]

/-- Complete interval computation for depth 15, residue 6821. -/
theorem bounds_15_6821 : exactInterval 15 6821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6821 : oddCount 6821 15 = 10 ∧ acceleratedOrbit 15 6821 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6821) = 3 ^ 10 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6821.1, data_15_6821.2]

/-- Complete interval computation for depth 15, residue 6822. -/
theorem bounds_15_6822 : exactInterval 15 6822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6822 : oddCount 6822 15 = 10 ∧ acceleratedOrbit 15 6822 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6822) = 3 ^ 10 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6822.1, data_15_6822.2]

/-- Complete interval computation for depth 15, residue 6823. -/
theorem bounds_15_6823 : exactInterval 15 6823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6823 : oddCount 6823 15 = 11 ∧ acceleratedOrbit 15 6823 = 36895 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6823) = 3 ^ 11 * m + 36895 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6823.1, data_15_6823.2]

/-- Complete interval computation for depth 15, residue 6824. -/
theorem bounds_15_6824 : exactInterval 15 6824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6824 : oddCount 6824 15 = 2 ∧ acceleratedOrbit 15 6824 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6824) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6824.1, data_15_6824.2]

/-- Complete interval computation for depth 15, residue 6825. -/
theorem bounds_15_6825 : exactInterval 15 6825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6825 : oddCount 6825 15 = 12 ∧ acceleratedOrbit 15 6825 = 110717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6825) = 3 ^ 12 * m + 110717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6825.1, data_15_6825.2]

/-- Complete interval computation for depth 15, residue 6826. -/
theorem bounds_15_6826 : exactInterval 15 6826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6826 : oddCount 6826 15 = 2 ∧ acceleratedOrbit 15 6826 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6826) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6826.1, data_15_6826.2]

/-- Complete interval computation for depth 15, residue 6827. -/
theorem bounds_15_6827 : exactInterval 15 6827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6827 : oddCount 6827 15 = 10 ∧ acceleratedOrbit 15 6827 = 12311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6827) = 3 ^ 10 * m + 12311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6827.1, data_15_6827.2]

/-- Complete interval computation for depth 15, residue 6828. -/
theorem bounds_15_6828 : exactInterval 15 6828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6828 : oddCount 6828 15 = 8 ∧ acceleratedOrbit 15 6828 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6828) = 3 ^ 8 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6828.1, data_15_6828.2]

/-- Complete interval computation for depth 15, residue 6829. -/
theorem bounds_15_6829 : exactInterval 15 6829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6829 : oddCount 6829 15 = 8 ∧ acceleratedOrbit 15 6829 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6829) = 3 ^ 8 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6829.1, data_15_6829.2]

/-- Complete interval computation for depth 15, residue 6830. -/
theorem bounds_15_6830 : exactInterval 15 6830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6830 : oddCount 6830 15 = 8 ∧ acceleratedOrbit 15 6830 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6830) = 3 ^ 8 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6830.1, data_15_6830.2]

/-- Complete interval computation for depth 15, residue 6831. -/
theorem bounds_15_6831 : exactInterval 15 6831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6831 : oddCount 6831 15 = 6 ∧ acceleratedOrbit 15 6831 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6831) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6831.1, data_15_6831.2]

/-- Complete interval computation for depth 15, residue 6832. -/
theorem bounds_15_6832 : exactInterval 15 6832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6832 : oddCount 6832 15 = 8 ∧ acceleratedOrbit 15 6832 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6832) = 3 ^ 8 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6832.1, data_15_6832.2]

/-- Complete interval computation for depth 15, residue 6833. -/
theorem bounds_15_6833 : exactInterval 15 6833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6833 : oddCount 6833 15 = 7 ∧ acceleratedOrbit 15 6833 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6833) = 3 ^ 7 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6833.1, data_15_6833.2]

/-- Complete interval computation for depth 15, residue 6834. -/
theorem bounds_15_6834 : exactInterval 15 6834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6834 : oddCount 6834 15 = 7 ∧ acceleratedOrbit 15 6834 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6834) = 3 ^ 7 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6834.1, data_15_6834.2]

/-- Complete interval computation for depth 15, residue 6835. -/
theorem bounds_15_6835 : exactInterval 15 6835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6835 : oddCount 6835 15 = 7 ∧ acceleratedOrbit 15 6835 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6835) = 3 ^ 7 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6835.1, data_15_6835.2]

/-- Complete interval computation for depth 15, residue 6836. -/
theorem bounds_15_6836 : exactInterval 15 6836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6836 : oddCount 6836 15 = 8 ∧ acceleratedOrbit 15 6836 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6836) = 3 ^ 8 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6836.1, data_15_6836.2]

/-- Complete interval computation for depth 15, residue 6837. -/
theorem bounds_15_6837 : exactInterval 15 6837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6837 : oddCount 6837 15 = 8 ∧ acceleratedOrbit 15 6837 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6837) = 3 ^ 8 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6837.1, data_15_6837.2]

/-- Complete interval computation for depth 15, residue 6838. -/
theorem bounds_15_6838 : exactInterval 15 6838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6838 : oddCount 6838 15 = 8 ∧ acceleratedOrbit 15 6838 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6838) = 3 ^ 8 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6838.1, data_15_6838.2]

/-- Complete interval computation for depth 15, residue 6839. -/
theorem bounds_15_6839 : exactInterval 15 6839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6839 : oddCount 6839 15 = 8 ∧ acceleratedOrbit 15 6839 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6839) = 3 ^ 8 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6839.1, data_15_6839.2]

/-- Complete interval computation for depth 15, residue 6840. -/
theorem bounds_15_6840 : exactInterval 15 6840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6840 : oddCount 6840 15 = 8 ∧ acceleratedOrbit 15 6840 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6840) = 3 ^ 8 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6840.1, data_15_6840.2]

/-- Complete interval computation for depth 15, residue 6841. -/
theorem bounds_15_6841 : exactInterval 15 6841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6841 : oddCount 6841 15 = 7 ∧ acceleratedOrbit 15 6841 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6841) = 3 ^ 7 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6841.1, data_15_6841.2]

/-- Complete interval computation for depth 15, residue 6842. -/
theorem bounds_15_6842 : exactInterval 15 6842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6842 : oddCount 6842 15 = 8 ∧ acceleratedOrbit 15 6842 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6842) = 3 ^ 8 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6842.1, data_15_6842.2]

/-- Complete interval computation for depth 15, residue 6843. -/
theorem bounds_15_6843 : exactInterval 15 6843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6843 : oddCount 6843 15 = 10 ∧ acceleratedOrbit 15 6843 = 12338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6843) = 3 ^ 10 * m + 12338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6843.1, data_15_6843.2]

/-- Complete interval computation for depth 15, residue 6844. -/
theorem bounds_15_6844 : exactInterval 15 6844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6844 : oddCount 6844 15 = 8 ∧ acceleratedOrbit 15 6844 = 1372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6844) = 3 ^ 8 * m + 1372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6844.1, data_15_6844.2]

/-- Complete interval computation for depth 15, residue 6845. -/
theorem bounds_15_6845 : exactInterval 15 6845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6845 : oddCount 6845 15 = 8 ∧ acceleratedOrbit 15 6845 = 1372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6845) = 3 ^ 8 * m + 1372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6845.1, data_15_6845.2]

/-- Complete interval computation for depth 15, residue 6846. -/
theorem bounds_15_6846 : exactInterval 15 6846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6846 : oddCount 6846 15 = 8 ∧ acceleratedOrbit 15 6846 = 1372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6846) = 3 ^ 8 * m + 1372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6846.1, data_15_6846.2]

/-- Complete interval computation for depth 15, residue 6847. -/
theorem bounds_15_6847 : exactInterval 15 6847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6847 : oddCount 6847 15 = 10 ∧ acceleratedOrbit 15 6847 = 12341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6847) = 3 ^ 10 * m + 12341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6847.1, data_15_6847.2]

end Collatz.Research.PassageAtlas.Batch0209
