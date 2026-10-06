import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0850

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27820. -/
theorem bounds_15_27820 : exactInterval 15 27820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27820 : oddCount 27820 15 = 7 ∧ acceleratedOrbit 15 27820 = 1858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27820) = 3 ^ 7 * m + 1858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27820.1, data_15_27820.2]

/-- Complete interval computation for depth 15, residue 27821. -/
theorem bounds_15_27821 : exactInterval 15 27821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27821 : oddCount 27821 15 = 7 ∧ acceleratedOrbit 15 27821 = 1858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27821) = 3 ^ 7 * m + 1858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27821.1, data_15_27821.2]

/-- Complete interval computation for depth 15, residue 27822. -/
theorem bounds_15_27822 : exactInterval 15 27822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27822 : oddCount 27822 15 = 7 ∧ acceleratedOrbit 15 27822 = 1858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27822) = 3 ^ 7 * m + 1858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27822.1, data_15_27822.2]

/-- Complete interval computation for depth 15, residue 27823. -/
theorem bounds_15_27823 : exactInterval 15 27823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27823 : oddCount 27823 15 = 9 ∧ acceleratedOrbit 15 27823 = 16714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27823) = 3 ^ 9 * m + 16714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27823.1, data_15_27823.2]

/-- Complete interval computation for depth 15, residue 27824. -/
theorem bounds_15_27824 : exactInterval 15 27824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27824 : oddCount 27824 15 = 7 ∧ acceleratedOrbit 15 27824 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27824) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27824.1, data_15_27824.2]

/-- Complete interval computation for depth 15, residue 27825. -/
theorem bounds_15_27825 : exactInterval 15 27825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27825 : oddCount 27825 15 = 7 ∧ acceleratedOrbit 15 27825 = 1858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27825) = 3 ^ 7 * m + 1858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27825.1, data_15_27825.2]

/-- Complete interval computation for depth 15, residue 27826. -/
theorem bounds_15_27826 : exactInterval 15 27826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27826 : oddCount 27826 15 = 7 ∧ acceleratedOrbit 15 27826 = 1858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27826) = 3 ^ 7 * m + 1858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27826.1, data_15_27826.2]

/-- Complete interval computation for depth 15, residue 27827. -/
theorem bounds_15_27827 : exactInterval 15 27827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27827 : oddCount 27827 15 = 7 ∧ acceleratedOrbit 15 27827 = 1858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27827) = 3 ^ 7 * m + 1858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27827.1, data_15_27827.2]

/-- Complete interval computation for depth 15, residue 27828. -/
theorem bounds_15_27828 : exactInterval 15 27828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27828 : oddCount 27828 15 = 7 ∧ acceleratedOrbit 15 27828 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27828) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27828.1, data_15_27828.2]

/-- Complete interval computation for depth 15, residue 27829. -/
theorem bounds_15_27829 : exactInterval 15 27829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27829 : oddCount 27829 15 = 7 ∧ acceleratedOrbit 15 27829 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27829) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27829.1, data_15_27829.2]

/-- Complete interval computation for depth 15, residue 27830. -/
theorem bounds_15_27830 : exactInterval 15 27830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27830 : oddCount 27830 15 = 8 ∧ acceleratedOrbit 15 27830 = 5573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27830) = 3 ^ 8 * m + 5573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27830.1, data_15_27830.2]

/-- Complete interval computation for depth 15, residue 27831. -/
theorem bounds_15_27831 : exactInterval 15 27831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27831 : oddCount 27831 15 = 8 ∧ acceleratedOrbit 15 27831 = 5573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27831) = 3 ^ 8 * m + 5573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27831.1, data_15_27831.2]

/-- Complete interval computation for depth 15, residue 27832. -/
theorem bounds_15_27832 : exactInterval 15 27832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27832 : oddCount 27832 15 = 7 ∧ acceleratedOrbit 15 27832 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27832) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27832.1, data_15_27832.2]

/-- Complete interval computation for depth 15, residue 27833. -/
theorem bounds_15_27833 : exactInterval 15 27833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27833 : oddCount 27833 15 = 10 ∧ acceleratedOrbit 15 27833 = 50165 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27833) = 3 ^ 10 * m + 50165 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27833.1, data_15_27833.2]

/-- Complete interval computation for depth 15, residue 27834. -/
theorem bounds_15_27834 : exactInterval 15 27834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27834 : oddCount 27834 15 = 7 ∧ acceleratedOrbit 15 27834 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27834) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27834.1, data_15_27834.2]

/-- Complete interval computation for depth 15, residue 27835. -/
theorem bounds_15_27835 : exactInterval 15 27835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27835 : oddCount 27835 15 = 10 ∧ acceleratedOrbit 15 27835 = 50165 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27835) = 3 ^ 10 * m + 50165 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27835.1, data_15_27835.2]

/-- Complete interval computation for depth 15, residue 27836. -/
theorem bounds_15_27836 : exactInterval 15 27836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27836 : oddCount 27836 15 = 8 ∧ acceleratedOrbit 15 27836 = 5575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27836) = 3 ^ 8 * m + 5575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27836.1, data_15_27836.2]

/-- Complete interval computation for depth 15, residue 27837. -/
theorem bounds_15_27837 : exactInterval 15 27837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27837 : oddCount 27837 15 = 8 ∧ acceleratedOrbit 15 27837 = 5575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27837) = 3 ^ 8 * m + 5575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27837.1, data_15_27837.2]

/-- Complete interval computation for depth 15, residue 27838. -/
theorem bounds_15_27838 : exactInterval 15 27838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27838 : oddCount 27838 15 = 8 ∧ acceleratedOrbit 15 27838 = 5575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27838) = 3 ^ 8 * m + 5575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27838.1, data_15_27838.2]

/-- Complete interval computation for depth 15, residue 27839. -/
theorem bounds_15_27839 : exactInterval 15 27839 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27839) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27839 : oddCount 27839 15 = 9 ∧ acceleratedOrbit 15 27839 = 16723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27839) = 3 ^ 9 * m + 16723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27839.1, data_15_27839.2]

/-- Complete interval computation for depth 15, residue 27840. -/
theorem bounds_15_27840 : exactInterval 15 27840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27840 : oddCount 27840 15 = 3 ∧ acceleratedOrbit 15 27840 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27840) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27840.1, data_15_27840.2]

/-- Complete interval computation for depth 15, residue 27841. -/
theorem bounds_15_27841 : exactInterval 15 27841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27841 : oddCount 27841 15 = 6 ∧ acceleratedOrbit 15 27841 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27841) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27841.1, data_15_27841.2]

/-- Complete interval computation for depth 15, residue 27842. -/
theorem bounds_15_27842 : exactInterval 15 27842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27842 : oddCount 27842 15 = 6 ∧ acceleratedOrbit 15 27842 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27842) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27842.1, data_15_27842.2]

/-- Complete interval computation for depth 15, residue 27843. -/
theorem bounds_15_27843 : exactInterval 15 27843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27843 : oddCount 27843 15 = 6 ∧ acceleratedOrbit 15 27843 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27843) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27843.1, data_15_27843.2]

/-- Complete interval computation for depth 15, residue 27844. -/
theorem bounds_15_27844 : exactInterval 15 27844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27844 : oddCount 27844 15 = 7 ∧ acceleratedOrbit 15 27844 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27844) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27844.1, data_15_27844.2]

/-- Complete interval computation for depth 15, residue 27845. -/
theorem bounds_15_27845 : exactInterval 15 27845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27845 : oddCount 27845 15 = 7 ∧ acceleratedOrbit 15 27845 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27845) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27845.1, data_15_27845.2]

/-- Complete interval computation for depth 15, residue 27846. -/
theorem bounds_15_27846 : exactInterval 15 27846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27846 : oddCount 27846 15 = 7 ∧ acceleratedOrbit 15 27846 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27846) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27846.1, data_15_27846.2]

/-- Complete interval computation for depth 15, residue 27847. -/
theorem bounds_15_27847 : exactInterval 15 27847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27847 : oddCount 27847 15 = 9 ∧ acceleratedOrbit 15 27847 = 16730 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27847) = 3 ^ 9 * m + 16730 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27847.1, data_15_27847.2]

/-- Complete interval computation for depth 15, residue 27848. -/
theorem bounds_15_27848 : exactInterval 15 27848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27848 : oddCount 27848 15 = 7 ∧ acceleratedOrbit 15 27848 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27848) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27848.1, data_15_27848.2]

/-- Complete interval computation for depth 15, residue 27849. -/
theorem bounds_15_27849 : exactInterval 15 27849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27849 : oddCount 27849 15 = 8 ∧ acceleratedOrbit 15 27849 = 5579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27849) = 3 ^ 8 * m + 5579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27849.1, data_15_27849.2]

/-- Complete interval computation for depth 15, residue 27850. -/
theorem bounds_15_27850 : exactInterval 15 27850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27850 : oddCount 27850 15 = 7 ∧ acceleratedOrbit 15 27850 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27850) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27850.1, data_15_27850.2]

/-- Complete interval computation for depth 15, residue 27851. -/
theorem bounds_15_27851 : exactInterval 15 27851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27851 : oddCount 27851 15 = 8 ∧ acceleratedOrbit 15 27851 = 5579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27851) = 3 ^ 8 * m + 5579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27851.1, data_15_27851.2]

end Collatz.Research.PassageAtlas.Batch0850
