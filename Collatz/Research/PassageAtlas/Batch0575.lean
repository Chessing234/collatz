import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0575

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18808. -/
theorem bounds_15_18808 : exactInterval 15 18808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18808 : oddCount 18808 15 = 7 ∧ acceleratedOrbit 15 18808 = 1256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18808) = 3 ^ 7 * m + 1256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18808.1, data_15_18808.2]

/-- Complete interval computation for depth 15, residue 18809. -/
theorem bounds_15_18809 : exactInterval 15 18809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18809 : oddCount 18809 15 = 12 ∧ acceleratedOrbit 15 18809 = 305086 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18809) = 3 ^ 12 * m + 305086 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18809.1, data_15_18809.2]

/-- Complete interval computation for depth 15, residue 18810. -/
theorem bounds_15_18810 : exactInterval 15 18810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18810 : oddCount 18810 15 = 7 ∧ acceleratedOrbit 15 18810 = 1256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18810) = 3 ^ 7 * m + 1256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18810.1, data_15_18810.2]

/-- Complete interval computation for depth 15, residue 18811. -/
theorem bounds_15_18811 : exactInterval 15 18811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18811 : oddCount 18811 15 = 8 ∧ acceleratedOrbit 15 18811 = 3767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18811) = 3 ^ 8 * m + 3767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18811.1, data_15_18811.2]

/-- Complete interval computation for depth 15, residue 18812. -/
theorem bounds_15_18812 : exactInterval 15 18812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18812 : oddCount 18812 15 = 7 ∧ acceleratedOrbit 15 18812 = 1256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18812) = 3 ^ 7 * m + 1256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18812.1, data_15_18812.2]

/-- Complete interval computation for depth 15, residue 18813. -/
theorem bounds_15_18813 : exactInterval 15 18813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18813 : oddCount 18813 15 = 7 ∧ acceleratedOrbit 15 18813 = 1256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18813) = 3 ^ 7 * m + 1256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18813.1, data_15_18813.2]

/-- Complete interval computation for depth 15, residue 18814. -/
theorem bounds_15_18814 : exactInterval 15 18814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18814 : oddCount 18814 15 = 9 ∧ acceleratedOrbit 15 18814 = 11303 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18814) = 3 ^ 9 * m + 11303 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18814.1, data_15_18814.2]

/-- Complete interval computation for depth 15, residue 18815. -/
theorem bounds_15_18815 : exactInterval 15 18815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18815 : oddCount 18815 15 = 9 ∧ acceleratedOrbit 15 18815 = 11303 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18815) = 3 ^ 9 * m + 11303 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18815.1, data_15_18815.2]

/-- Complete interval computation for depth 15, residue 18816. -/
theorem bounds_15_18816 : exactInterval 15 18816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18816 : oddCount 18816 15 = 4 ∧ acceleratedOrbit 15 18816 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18816) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18816.1, data_15_18816.2]

/-- Complete interval computation for depth 15, residue 18817. -/
theorem bounds_15_18817 : exactInterval 15 18817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18817 : oddCount 18817 15 = 8 ∧ acceleratedOrbit 15 18817 = 3770 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18817) = 3 ^ 8 * m + 3770 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18817.1, data_15_18817.2]

/-- Complete interval computation for depth 15, residue 18818. -/
theorem bounds_15_18818 : exactInterval 15 18818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18818 : oddCount 18818 15 = 6 ∧ acceleratedOrbit 15 18818 = 419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18818) = 3 ^ 6 * m + 419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18818.1, data_15_18818.2]

/-- Complete interval computation for depth 15, residue 18819. -/
theorem bounds_15_18819 : exactInterval 15 18819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18819 : oddCount 18819 15 = 6 ∧ acceleratedOrbit 15 18819 = 419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18819) = 3 ^ 6 * m + 419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18819.1, data_15_18819.2]

/-- Complete interval computation for depth 15, residue 18820. -/
theorem bounds_15_18820 : exactInterval 15 18820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18820 : oddCount 18820 15 = 6 ∧ acceleratedOrbit 15 18820 = 419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18820) = 3 ^ 6 * m + 419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18820.1, data_15_18820.2]

/-- Complete interval computation for depth 15, residue 18821. -/
theorem bounds_15_18821 : exactInterval 15 18821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18821 : oddCount 18821 15 = 6 ∧ acceleratedOrbit 15 18821 = 419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18821) = 3 ^ 6 * m + 419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18821.1, data_15_18821.2]

/-- Complete interval computation for depth 15, residue 18822. -/
theorem bounds_15_18822 : exactInterval 15 18822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18822 : oddCount 18822 15 = 6 ∧ acceleratedOrbit 15 18822 = 419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18822) = 3 ^ 6 * m + 419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18822.1, data_15_18822.2]

/-- Complete interval computation for depth 15, residue 18823. -/
theorem bounds_15_18823 : exactInterval 15 18823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18823 : oddCount 18823 15 = 6 ∧ acceleratedOrbit 15 18823 = 419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18823) = 3 ^ 6 * m + 419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18823.1, data_15_18823.2]

/-- Complete interval computation for depth 15, residue 18824. -/
theorem bounds_15_18824 : exactInterval 15 18824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18824 : oddCount 18824 15 = 5 ∧ acceleratedOrbit 15 18824 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18824) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18824.1, data_15_18824.2]

/-- Complete interval computation for depth 15, residue 18825. -/
theorem bounds_15_18825 : exactInterval 15 18825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18825 : oddCount 18825 15 = 10 ∧ acceleratedOrbit 15 18825 = 33929 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18825) = 3 ^ 10 * m + 33929 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18825.1, data_15_18825.2]

/-- Complete interval computation for depth 15, residue 18826. -/
theorem bounds_15_18826 : exactInterval 15 18826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18826 : oddCount 18826 15 = 5 ∧ acceleratedOrbit 15 18826 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18826) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18826.1, data_15_18826.2]

/-- Complete interval computation for depth 15, residue 18827. -/
theorem bounds_15_18827 : exactInterval 15 18827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18827 : oddCount 18827 15 = 9 ∧ acceleratedOrbit 15 18827 = 11312 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18827) = 3 ^ 9 * m + 11312 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18827.1, data_15_18827.2]

/-- Complete interval computation for depth 15, residue 18828. -/
theorem bounds_15_18828 : exactInterval 15 18828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18828 : oddCount 18828 15 = 5 ∧ acceleratedOrbit 15 18828 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18828) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18828.1, data_15_18828.2]

/-- Complete interval computation for depth 15, residue 18829. -/
theorem bounds_15_18829 : exactInterval 15 18829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18829 : oddCount 18829 15 = 5 ∧ acceleratedOrbit 15 18829 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18829) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18829.1, data_15_18829.2]

/-- Complete interval computation for depth 15, residue 18830. -/
theorem bounds_15_18830 : exactInterval 15 18830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18830 : oddCount 18830 15 = 6 ∧ acceleratedOrbit 15 18830 = 419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18830) = 3 ^ 6 * m + 419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18830.1, data_15_18830.2]

/-- Complete interval computation for depth 15, residue 18831. -/
theorem bounds_15_18831 : exactInterval 15 18831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18831 : oddCount 18831 15 = 6 ∧ acceleratedOrbit 15 18831 = 419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18831) = 3 ^ 6 * m + 419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18831.1, data_15_18831.2]

/-- Complete interval computation for depth 15, residue 18832. -/
theorem bounds_15_18832 : exactInterval 15 18832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18832 : oddCount 18832 15 = 5 ∧ acceleratedOrbit 15 18832 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18832) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18832.1, data_15_18832.2]

/-- Complete interval computation for depth 15, residue 18833. -/
theorem bounds_15_18833 : exactInterval 15 18833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18833 : oddCount 18833 15 = 7 ∧ acceleratedOrbit 15 18833 = 1259 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18833) = 3 ^ 7 * m + 1259 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18833.1, data_15_18833.2]

/-- Complete interval computation for depth 15, residue 18834. -/
theorem bounds_15_18834 : exactInterval 15 18834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18834 : oddCount 18834 15 = 7 ∧ acceleratedOrbit 15 18834 = 1259 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18834) = 3 ^ 7 * m + 1259 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18834.1, data_15_18834.2]

/-- Complete interval computation for depth 15, residue 18835. -/
theorem bounds_15_18835 : exactInterval 15 18835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18835 : oddCount 18835 15 = 7 ∧ acceleratedOrbit 15 18835 = 1259 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18835) = 3 ^ 7 * m + 1259 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18835.1, data_15_18835.2]

/-- Complete interval computation for depth 15, residue 18836. -/
theorem bounds_15_18836 : exactInterval 15 18836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18836 : oddCount 18836 15 = 5 ∧ acceleratedOrbit 15 18836 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18836) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18836.1, data_15_18836.2]

/-- Complete interval computation for depth 15, residue 18837. -/
theorem bounds_15_18837 : exactInterval 15 18837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18837 : oddCount 18837 15 = 5 ∧ acceleratedOrbit 15 18837 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18837) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18837.1, data_15_18837.2]

/-- Complete interval computation for depth 15, residue 18838. -/
theorem bounds_15_18838 : exactInterval 15 18838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18838 : oddCount 18838 15 = 7 ∧ acceleratedOrbit 15 18838 = 1259 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18838) = 3 ^ 7 * m + 1259 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18838.1, data_15_18838.2]

/-- Complete interval computation for depth 15, residue 18839. -/
theorem bounds_15_18839 : exactInterval 15 18839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18839 : oddCount 18839 15 = 7 ∧ acceleratedOrbit 15 18839 = 1259 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18839) = 3 ^ 7 * m + 1259 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18839.1, data_15_18839.2]

/-- Complete interval computation for depth 15, residue 18840. -/
theorem bounds_15_18840 : exactInterval 15 18840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18840 : oddCount 18840 15 = 5 ∧ acceleratedOrbit 15 18840 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18840) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18840.1, data_15_18840.2]

end Collatz.Research.PassageAtlas.Batch0575
