import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0453

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14811. -/
theorem bounds_15_14811 : exactInterval 15 14811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14811 : oddCount 14811 15 = 9 ∧ acceleratedOrbit 15 14811 = 8900 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14811) = 3 ^ 9 * m + 8900 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14811.1, data_15_14811.2]

/-- Complete interval computation for depth 15, residue 14812. -/
theorem bounds_15_14812 : exactInterval 15 14812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14812 : oddCount 14812 15 = 5 ∧ acceleratedOrbit 15 14812 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14812) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14812.1, data_15_14812.2]

/-- Complete interval computation for depth 15, residue 14813. -/
theorem bounds_15_14813 : exactInterval 15 14813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14813 : oddCount 14813 15 = 5 ∧ acceleratedOrbit 15 14813 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14813) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14813.1, data_15_14813.2]

/-- Complete interval computation for depth 15, residue 14814. -/
theorem bounds_15_14814 : exactInterval 15 14814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14814 : oddCount 14814 15 = 11 ∧ acceleratedOrbit 15 14814 = 80099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14814) = 3 ^ 11 * m + 80099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14814.1, data_15_14814.2]

/-- Complete interval computation for depth 15, residue 14815. -/
theorem bounds_15_14815 : exactInterval 15 14815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14815 : oddCount 14815 15 = 11 ∧ acceleratedOrbit 15 14815 = 80099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14815) = 3 ^ 11 * m + 80099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14815.1, data_15_14815.2]

/-- Complete interval computation for depth 15, residue 14816. -/
theorem bounds_15_14816 : exactInterval 15 14816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14816 : oddCount 14816 15 = 7 ∧ acceleratedOrbit 15 14816 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14816) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14816.1, data_15_14816.2]

/-- Complete interval computation for depth 15, residue 14817. -/
theorem bounds_15_14817 : exactInterval 15 14817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14817 : oddCount 14817 15 = 9 ∧ acceleratedOrbit 15 14817 = 8903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14817) = 3 ^ 9 * m + 8903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14817.1, data_15_14817.2]

/-- Complete interval computation for depth 15, residue 14818. -/
theorem bounds_15_14818 : exactInterval 15 14818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14818 : oddCount 14818 15 = 7 ∧ acceleratedOrbit 15 14818 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14818) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14818.1, data_15_14818.2]

/-- Complete interval computation for depth 15, residue 14819. -/
theorem bounds_15_14819 : exactInterval 15 14819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14819 : oddCount 14819 15 = 7 ∧ acceleratedOrbit 15 14819 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14819) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14819.1, data_15_14819.2]

/-- Complete interval computation for depth 15, residue 14820. -/
theorem bounds_15_14820 : exactInterval 15 14820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14820 : oddCount 14820 15 = 9 ∧ acceleratedOrbit 15 14820 = 8909 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14820) = 3 ^ 9 * m + 8909 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14820.1, data_15_14820.2]

/-- Complete interval computation for depth 15, residue 14821. -/
theorem bounds_15_14821 : exactInterval 15 14821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14821 : oddCount 14821 15 = 9 ∧ acceleratedOrbit 15 14821 = 8909 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14821) = 3 ^ 9 * m + 8909 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14821.1, data_15_14821.2]

/-- Complete interval computation for depth 15, residue 14822. -/
theorem bounds_15_14822 : exactInterval 15 14822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14822 : oddCount 14822 15 = 9 ∧ acceleratedOrbit 15 14822 = 8909 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14822) = 3 ^ 9 * m + 8909 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14822.1, data_15_14822.2]

/-- Complete interval computation for depth 15, residue 14823. -/
theorem bounds_15_14823 : exactInterval 15 14823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14823 : oddCount 14823 15 = 9 ∧ acceleratedOrbit 15 14823 = 8905 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14823) = 3 ^ 9 * m + 8905 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14823.1, data_15_14823.2]

/-- Complete interval computation for depth 15, residue 14824. -/
theorem bounds_15_14824 : exactInterval 15 14824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14824 : oddCount 14824 15 = 7 ∧ acceleratedOrbit 15 14824 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14824) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14824.1, data_15_14824.2]

/-- Complete interval computation for depth 15, residue 14825. -/
theorem bounds_15_14825 : exactInterval 15 14825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14825 : oddCount 14825 15 = 10 ∧ acceleratedOrbit 15 14825 = 26720 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14825) = 3 ^ 10 * m + 26720 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14825.1, data_15_14825.2]

/-- Complete interval computation for depth 15, residue 14826. -/
theorem bounds_15_14826 : exactInterval 15 14826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14826 : oddCount 14826 15 = 7 ∧ acceleratedOrbit 15 14826 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14826) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14826.1, data_15_14826.2]

/-- Complete interval computation for depth 15, residue 14827. -/
theorem bounds_15_14827 : exactInterval 15 14827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14827 : oddCount 14827 15 = 10 ∧ acceleratedOrbit 15 14827 = 26723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14827) = 3 ^ 10 * m + 26723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14827.1, data_15_14827.2]

/-- Complete interval computation for depth 15, residue 14828. -/
theorem bounds_15_14828 : exactInterval 15 14828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14828 : oddCount 14828 15 = 5 ∧ acceleratedOrbit 15 14828 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14828) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14828.1, data_15_14828.2]

/-- Complete interval computation for depth 15, residue 14829. -/
theorem bounds_15_14829 : exactInterval 15 14829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14829 : oddCount 14829 15 = 5 ∧ acceleratedOrbit 15 14829 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14829) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14829.1, data_15_14829.2]

/-- Complete interval computation for depth 15, residue 14830. -/
theorem bounds_15_14830 : exactInterval 15 14830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14830 : oddCount 14830 15 = 5 ∧ acceleratedOrbit 15 14830 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14830) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14830.1, data_15_14830.2]

/-- Complete interval computation for depth 15, residue 14831. -/
theorem bounds_15_14831 : exactInterval 15 14831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14831 : oddCount 14831 15 = 11 ∧ acceleratedOrbit 15 14831 = 80185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14831) = 3 ^ 11 * m + 80185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14831.1, data_15_14831.2]

/-- Complete interval computation for depth 15, residue 14832. -/
theorem bounds_15_14832 : exactInterval 15 14832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14832 : oddCount 14832 15 = 7 ∧ acceleratedOrbit 15 14832 = 991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14832) = 3 ^ 7 * m + 991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14832.1, data_15_14832.2]

/-- Complete interval computation for depth 15, residue 14833. -/
theorem bounds_15_14833 : exactInterval 15 14833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14833 : oddCount 14833 15 = 7 ∧ acceleratedOrbit 15 14833 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14833) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14833.1, data_15_14833.2]

/-- Complete interval computation for depth 15, residue 14834. -/
theorem bounds_15_14834 : exactInterval 15 14834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14834 : oddCount 14834 15 = 8 ∧ acceleratedOrbit 15 14834 = 2972 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14834) = 3 ^ 8 * m + 2972 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14834.1, data_15_14834.2]

/-- Complete interval computation for depth 15, residue 14835. -/
theorem bounds_15_14835 : exactInterval 15 14835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14835 : oddCount 14835 15 = 8 ∧ acceleratedOrbit 15 14835 = 2972 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14835) = 3 ^ 8 * m + 2972 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14835.1, data_15_14835.2]

/-- Complete interval computation for depth 15, residue 14836. -/
theorem bounds_15_14836 : exactInterval 15 14836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14836 : oddCount 14836 15 = 7 ∧ acceleratedOrbit 15 14836 = 991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14836) = 3 ^ 7 * m + 991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14836.1, data_15_14836.2]

/-- Complete interval computation for depth 15, residue 14837. -/
theorem bounds_15_14837 : exactInterval 15 14837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14837 : oddCount 14837 15 = 7 ∧ acceleratedOrbit 15 14837 = 991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14837) = 3 ^ 7 * m + 991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14837.1, data_15_14837.2]

/-- Complete interval computation for depth 15, residue 14838. -/
theorem bounds_15_14838 : exactInterval 15 14838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14838 : oddCount 14838 15 = 9 ∧ acceleratedOrbit 15 14838 = 8915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14838) = 3 ^ 9 * m + 8915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14838.1, data_15_14838.2]

/-- Complete interval computation for depth 15, residue 14839. -/
theorem bounds_15_14839 : exactInterval 15 14839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14839 : oddCount 14839 15 = 9 ∧ acceleratedOrbit 15 14839 = 8915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14839) = 3 ^ 9 * m + 8915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14839.1, data_15_14839.2]

/-- Complete interval computation for depth 15, residue 14840. -/
theorem bounds_15_14840 : exactInterval 15 14840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14840 : oddCount 14840 15 = 7 ∧ acceleratedOrbit 15 14840 = 991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14840) = 3 ^ 7 * m + 991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14840.1, data_15_14840.2]

/-- Complete interval computation for depth 15, residue 14841. -/
theorem bounds_15_14841 : exactInterval 15 14841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14841 : oddCount 14841 15 = 10 ∧ acceleratedOrbit 15 14841 = 26750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14841) = 3 ^ 10 * m + 26750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14841.1, data_15_14841.2]

/-- Complete interval computation for depth 15, residue 14842. -/
theorem bounds_15_14842 : exactInterval 15 14842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14842 : oddCount 14842 15 = 7 ∧ acceleratedOrbit 15 14842 = 991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14842) = 3 ^ 7 * m + 991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14842.1, data_15_14842.2]

end Collatz.Research.PassageAtlas.Batch0453
