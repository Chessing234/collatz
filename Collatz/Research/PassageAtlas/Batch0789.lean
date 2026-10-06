import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0789

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25821. -/
theorem bounds_15_25821 : exactInterval 15 25821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25821 : oddCount 25821 15 = 9 ∧ acceleratedOrbit 15 25821 = 15515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25821) = 3 ^ 9 * m + 15515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25821.1, data_15_25821.2]

/-- Complete interval computation for depth 15, residue 25822. -/
theorem bounds_15_25822 : exactInterval 15 25822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25822 : oddCount 25822 15 = 10 ∧ acceleratedOrbit 15 25822 = 46538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25822) = 3 ^ 10 * m + 46538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25822.1, data_15_25822.2]

/-- Complete interval computation for depth 15, residue 25823. -/
theorem bounds_15_25823 : exactInterval 15 25823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25823 : oddCount 25823 15 = 10 ∧ acceleratedOrbit 15 25823 = 46538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25823) = 3 ^ 10 * m + 46538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25823.1, data_15_25823.2]

/-- Complete interval computation for depth 15, residue 25824. -/
theorem bounds_15_25824 : exactInterval 15 25824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25824 : oddCount 25824 15 = 7 ∧ acceleratedOrbit 15 25824 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25824) = 3 ^ 7 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25824.1, data_15_25824.2]

/-- Complete interval computation for depth 15, residue 25825. -/
theorem bounds_15_25825 : exactInterval 15 25825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25825 : oddCount 25825 15 = 9 ∧ acceleratedOrbit 15 25825 = 15514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25825) = 3 ^ 9 * m + 15514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25825.1, data_15_25825.2]

/-- Complete interval computation for depth 15, residue 25826. -/
theorem bounds_15_25826 : exactInterval 15 25826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25826 : oddCount 25826 15 = 4 ∧ acceleratedOrbit 15 25826 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25826) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25826.1, data_15_25826.2]

/-- Complete interval computation for depth 15, residue 25827. -/
theorem bounds_15_25827 : exactInterval 15 25827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25827 : oddCount 25827 15 = 4 ∧ acceleratedOrbit 15 25827 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25827) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25827.1, data_15_25827.2]

/-- Complete interval computation for depth 15, residue 25828. -/
theorem bounds_15_25828 : exactInterval 15 25828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25828 : oddCount 25828 15 = 8 ∧ acceleratedOrbit 15 25828 = 5174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25828) = 3 ^ 8 * m + 5174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25828.1, data_15_25828.2]

/-- Complete interval computation for depth 15, residue 25829. -/
theorem bounds_15_25829 : exactInterval 15 25829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25829 : oddCount 25829 15 = 8 ∧ acceleratedOrbit 15 25829 = 5174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25829) = 3 ^ 8 * m + 5174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25829.1, data_15_25829.2]

/-- Complete interval computation for depth 15, residue 25830. -/
theorem bounds_15_25830 : exactInterval 15 25830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25830 : oddCount 25830 15 = 8 ∧ acceleratedOrbit 15 25830 = 5174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25830) = 3 ^ 8 * m + 5174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25830.1, data_15_25830.2]

/-- Complete interval computation for depth 15, residue 25831. -/
theorem bounds_15_25831 : exactInterval 15 25831 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25831) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25831 : oddCount 25831 15 = 9 ∧ acceleratedOrbit 15 25831 = 15517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25831) = 3 ^ 9 * m + 15517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25831.1, data_15_25831.2]

/-- Complete interval computation for depth 15, residue 25832. -/
theorem bounds_15_25832 : exactInterval 15 25832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25832 : oddCount 25832 15 = 7 ∧ acceleratedOrbit 15 25832 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25832) = 3 ^ 7 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25832.1, data_15_25832.2]

/-- Complete interval computation for depth 15, residue 25833. -/
theorem bounds_15_25833 : exactInterval 15 25833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25833 : oddCount 25833 15 = 8 ∧ acceleratedOrbit 15 25833 = 5174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25833) = 3 ^ 8 * m + 5174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25833.1, data_15_25833.2]

/-- Complete interval computation for depth 15, residue 25834. -/
theorem bounds_15_25834 : exactInterval 15 25834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25834 : oddCount 25834 15 = 7 ∧ acceleratedOrbit 15 25834 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25834) = 3 ^ 7 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25834.1, data_15_25834.2]

/-- Complete interval computation for depth 15, residue 25835. -/
theorem bounds_15_25835 : exactInterval 15 25835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25835 : oddCount 25835 15 = 9 ∧ acceleratedOrbit 15 25835 = 15520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25835) = 3 ^ 9 * m + 15520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25835.1, data_15_25835.2]

/-- Complete interval computation for depth 15, residue 25836. -/
theorem bounds_15_25836 : exactInterval 15 25836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25836 : oddCount 25836 15 = 7 ∧ acceleratedOrbit 15 25836 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25836) = 3 ^ 7 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25836.1, data_15_25836.2]

/-- Complete interval computation for depth 15, residue 25837. -/
theorem bounds_15_25837 : exactInterval 15 25837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25837 : oddCount 25837 15 = 7 ∧ acceleratedOrbit 15 25837 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25837) = 3 ^ 7 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25837.1, data_15_25837.2]

/-- Complete interval computation for depth 15, residue 25838. -/
theorem bounds_15_25838 : exactInterval 15 25838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25838 : oddCount 25838 15 = 7 ∧ acceleratedOrbit 15 25838 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25838) = 3 ^ 7 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25838.1, data_15_25838.2]

/-- Complete interval computation for depth 15, residue 25839. -/
theorem bounds_15_25839 : exactInterval 15 25839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25839 : oddCount 25839 15 = 12 ∧ acceleratedOrbit 15 25839 = 419084 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25839) = 3 ^ 12 * m + 419084 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25839.1, data_15_25839.2]

/-- Complete interval computation for depth 15, residue 25840. -/
theorem bounds_15_25840 : exactInterval 15 25840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25840 : oddCount 25840 15 = 7 ∧ acceleratedOrbit 15 25840 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25840) = 3 ^ 7 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25840.1, data_15_25840.2]

/-- Complete interval computation for depth 15, residue 25841. -/
theorem bounds_15_25841 : exactInterval 15 25841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25841 : oddCount 25841 15 = 7 ∧ acceleratedOrbit 15 25841 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25841) = 3 ^ 7 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25841.1, data_15_25841.2]

/-- Complete interval computation for depth 15, residue 25842. -/
theorem bounds_15_25842 : exactInterval 15 25842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25842 : oddCount 25842 15 = 6 ∧ acceleratedOrbit 15 25842 = 575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25842) = 3 ^ 6 * m + 575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25842.1, data_15_25842.2]

/-- Complete interval computation for depth 15, residue 25843. -/
theorem bounds_15_25843 : exactInterval 15 25843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25843 : oddCount 25843 15 = 6 ∧ acceleratedOrbit 15 25843 = 575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25843) = 3 ^ 6 * m + 575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25843.1, data_15_25843.2]

/-- Complete interval computation for depth 15, residue 25844. -/
theorem bounds_15_25844 : exactInterval 15 25844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25844 : oddCount 25844 15 = 7 ∧ acceleratedOrbit 15 25844 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25844) = 3 ^ 7 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25844.1, data_15_25844.2]

/-- Complete interval computation for depth 15, residue 25845. -/
theorem bounds_15_25845 : exactInterval 15 25845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25845 : oddCount 25845 15 = 7 ∧ acceleratedOrbit 15 25845 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25845) = 3 ^ 7 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25845.1, data_15_25845.2]

/-- Complete interval computation for depth 15, residue 25846. -/
theorem bounds_15_25846 : exactInterval 15 25846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25846 : oddCount 25846 15 = 8 ∧ acceleratedOrbit 15 25846 = 5177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25846) = 3 ^ 8 * m + 5177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25846.1, data_15_25846.2]

/-- Complete interval computation for depth 15, residue 25847. -/
theorem bounds_15_25847 : exactInterval 15 25847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25847 : oddCount 25847 15 = 8 ∧ acceleratedOrbit 15 25847 = 5177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25847) = 3 ^ 8 * m + 5177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25847.1, data_15_25847.2]

/-- Complete interval computation for depth 15, residue 25848. -/
theorem bounds_15_25848 : exactInterval 15 25848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25848 : oddCount 25848 15 = 10 ∧ acceleratedOrbit 15 25848 = 46595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25848) = 3 ^ 10 * m + 46595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25848.1, data_15_25848.2]

/-- Complete interval computation for depth 15, residue 25849. -/
theorem bounds_15_25849 : exactInterval 15 25849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25849 : oddCount 25849 15 = 8 ∧ acceleratedOrbit 15 25849 = 5177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25849) = 3 ^ 8 * m + 5177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25849.1, data_15_25849.2]

/-- Complete interval computation for depth 15, residue 25850. -/
theorem bounds_15_25850 : exactInterval 15 25850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25850 : oddCount 25850 15 = 10 ∧ acceleratedOrbit 15 25850 = 46595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25850) = 3 ^ 10 * m + 46595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25850.1, data_15_25850.2]

/-- Complete interval computation for depth 15, residue 25851. -/
theorem bounds_15_25851 : exactInterval 15 25851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25851 : oddCount 25851 15 = 10 ∧ acceleratedOrbit 15 25851 = 46588 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25851) = 3 ^ 10 * m + 46588 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25851.1, data_15_25851.2]

/-- Complete interval computation for depth 15, residue 25852. -/
theorem bounds_15_25852 : exactInterval 15 25852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25852 : oddCount 25852 15 = 10 ∧ acceleratedOrbit 15 25852 = 46595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25852) = 3 ^ 10 * m + 46595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25852.1, data_15_25852.2]

end Collatz.Research.PassageAtlas.Batch0789
