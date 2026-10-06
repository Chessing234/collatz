import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0728

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23822. -/
theorem bounds_15_23822 : exactInterval 15 23822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23822 : oddCount 23822 15 = 8 ∧ acceleratedOrbit 15 23822 = 4772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23822) = 3 ^ 8 * m + 4772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23822.1, data_15_23822.2]

/-- Complete interval computation for depth 15, residue 23823. -/
theorem bounds_15_23823 : exactInterval 15 23823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23823 : oddCount 23823 15 = 8 ∧ acceleratedOrbit 15 23823 = 4772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23823) = 3 ^ 8 * m + 4772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23823.1, data_15_23823.2]

/-- Complete interval computation for depth 15, residue 23824. -/
theorem bounds_15_23824 : exactInterval 15 23824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23824 : oddCount 23824 15 = 4 ∧ acceleratedOrbit 15 23824 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23824) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23824.1, data_15_23824.2]

/-- Complete interval computation for depth 15, residue 23825. -/
theorem bounds_15_23825 : exactInterval 15 23825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23825 : oddCount 23825 15 = 7 ∧ acceleratedOrbit 15 23825 = 1592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23825) = 3 ^ 7 * m + 1592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23825.1, data_15_23825.2]

/-- Complete interval computation for depth 15, residue 23826. -/
theorem bounds_15_23826 : exactInterval 15 23826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23826 : oddCount 23826 15 = 10 ∧ acceleratedOrbit 15 23826 = 42943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23826) = 3 ^ 10 * m + 42943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23826.1, data_15_23826.2]

/-- Complete interval computation for depth 15, residue 23827. -/
theorem bounds_15_23827 : exactInterval 15 23827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23827 : oddCount 23827 15 = 10 ∧ acceleratedOrbit 15 23827 = 42943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23827) = 3 ^ 10 * m + 42943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23827.1, data_15_23827.2]

/-- Complete interval computation for depth 15, residue 23828. -/
theorem bounds_15_23828 : exactInterval 15 23828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23828 : oddCount 23828 15 = 4 ∧ acceleratedOrbit 15 23828 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23828) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23828.1, data_15_23828.2]

/-- Complete interval computation for depth 15, residue 23829. -/
theorem bounds_15_23829 : exactInterval 15 23829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23829 : oddCount 23829 15 = 4 ∧ acceleratedOrbit 15 23829 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23829) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23829.1, data_15_23829.2]

/-- Complete interval computation for depth 15, residue 23830. -/
theorem bounds_15_23830 : exactInterval 15 23830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23830 : oddCount 23830 15 = 7 ∧ acceleratedOrbit 15 23830 = 1592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23830) = 3 ^ 7 * m + 1592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23830.1, data_15_23830.2]

/-- Complete interval computation for depth 15, residue 23831. -/
theorem bounds_15_23831 : exactInterval 15 23831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23831 : oddCount 23831 15 = 7 ∧ acceleratedOrbit 15 23831 = 1592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23831) = 3 ^ 7 * m + 1592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23831.1, data_15_23831.2]

/-- Complete interval computation for depth 15, residue 23832. -/
theorem bounds_15_23832 : exactInterval 15 23832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23832 : oddCount 23832 15 = 4 ∧ acceleratedOrbit 15 23832 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23832) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23832.1, data_15_23832.2]

/-- Complete interval computation for depth 15, residue 23833. -/
theorem bounds_15_23833 : exactInterval 15 23833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23833 : oddCount 23833 15 = 10 ∧ acceleratedOrbit 15 23833 = 42956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23833) = 3 ^ 10 * m + 42956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23833.1, data_15_23833.2]

/-- Complete interval computation for depth 15, residue 23834. -/
theorem bounds_15_23834 : exactInterval 15 23834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23834 : oddCount 23834 15 = 4 ∧ acceleratedOrbit 15 23834 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23834) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23834.1, data_15_23834.2]

/-- Complete interval computation for depth 15, residue 23835. -/
theorem bounds_15_23835 : exactInterval 15 23835 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23835) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23835 : oddCount 23835 15 = 9 ∧ acceleratedOrbit 15 23835 = 14318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23835) = 3 ^ 9 * m + 14318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23835.1, data_15_23835.2]

/-- Complete interval computation for depth 15, residue 23836. -/
theorem bounds_15_23836 : exactInterval 15 23836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23836 : oddCount 23836 15 = 8 ∧ acceleratedOrbit 15 23836 = 4774 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23836) = 3 ^ 8 * m + 4774 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23836.1, data_15_23836.2]

/-- Complete interval computation for depth 15, residue 23837. -/
theorem bounds_15_23837 : exactInterval 15 23837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23837 : oddCount 23837 15 = 8 ∧ acceleratedOrbit 15 23837 = 4774 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23837) = 3 ^ 8 * m + 4774 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23837.1, data_15_23837.2]

/-- Complete interval computation for depth 15, residue 23838. -/
theorem bounds_15_23838 : exactInterval 15 23838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23838 : oddCount 23838 15 = 8 ∧ acceleratedOrbit 15 23838 = 4774 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23838) = 3 ^ 8 * m + 4774 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23838.1, data_15_23838.2]

/-- Complete interval computation for depth 15, residue 23839. -/
theorem bounds_15_23839 : exactInterval 15 23839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23839 : oddCount 23839 15 = 8 ∧ acceleratedOrbit 15 23839 = 4774 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23839) = 3 ^ 8 * m + 4774 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23839.1, data_15_23839.2]

/-- Complete interval computation for depth 15, residue 23840. -/
theorem bounds_15_23840 : exactInterval 15 23840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23840 : oddCount 23840 15 = 7 ∧ acceleratedOrbit 15 23840 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23840) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23840.1, data_15_23840.2]

/-- Complete interval computation for depth 15, residue 23841. -/
theorem bounds_15_23841 : exactInterval 15 23841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23841 : oddCount 23841 15 = 8 ∧ acceleratedOrbit 15 23841 = 4778 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23841) = 3 ^ 8 * m + 4778 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23841.1, data_15_23841.2]

/-- Complete interval computation for depth 15, residue 23842. -/
theorem bounds_15_23842 : exactInterval 15 23842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23842 : oddCount 23842 15 = 8 ∧ acceleratedOrbit 15 23842 = 4778 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23842) = 3 ^ 8 * m + 4778 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23842.1, data_15_23842.2]

/-- Complete interval computation for depth 15, residue 23843. -/
theorem bounds_15_23843 : exactInterval 15 23843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23843 : oddCount 23843 15 = 8 ∧ acceleratedOrbit 15 23843 = 4778 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23843) = 3 ^ 8 * m + 4778 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23843.1, data_15_23843.2]

/-- Complete interval computation for depth 15, residue 23844. -/
theorem bounds_15_23844 : exactInterval 15 23844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23844 : oddCount 23844 15 = 8 ∧ acceleratedOrbit 15 23844 = 4778 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23844) = 3 ^ 8 * m + 4778 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23844.1, data_15_23844.2]

/-- Complete interval computation for depth 15, residue 23845. -/
theorem bounds_15_23845 : exactInterval 15 23845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23845 : oddCount 23845 15 = 8 ∧ acceleratedOrbit 15 23845 = 4778 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23845) = 3 ^ 8 * m + 4778 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23845.1, data_15_23845.2]

/-- Complete interval computation for depth 15, residue 23846. -/
theorem bounds_15_23846 : exactInterval 15 23846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23846 : oddCount 23846 15 = 8 ∧ acceleratedOrbit 15 23846 = 4778 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23846) = 3 ^ 8 * m + 4778 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23846.1, data_15_23846.2]

/-- Complete interval computation for depth 15, residue 23847. -/
theorem bounds_15_23847 : exactInterval 15 23847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23847 : oddCount 23847 15 = 9 ∧ acceleratedOrbit 15 23847 = 14327 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23847) = 3 ^ 9 * m + 14327 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23847.1, data_15_23847.2]

/-- Complete interval computation for depth 15, residue 23848. -/
theorem bounds_15_23848 : exactInterval 15 23848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23848 : oddCount 23848 15 = 7 ∧ acceleratedOrbit 15 23848 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23848) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23848.1, data_15_23848.2]

/-- Complete interval computation for depth 15, residue 23849. -/
theorem bounds_15_23849 : exactInterval 15 23849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23849 : oddCount 23849 15 = 11 ∧ acceleratedOrbit 15 23849 = 128942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23849) = 3 ^ 11 * m + 128942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23849.1, data_15_23849.2]

/-- Complete interval computation for depth 15, residue 23850. -/
theorem bounds_15_23850 : exactInterval 15 23850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23850 : oddCount 23850 15 = 7 ∧ acceleratedOrbit 15 23850 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23850) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23850.1, data_15_23850.2]

/-- Complete interval computation for depth 15, residue 23851. -/
theorem bounds_15_23851 : exactInterval 15 23851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23851 : oddCount 23851 15 = 9 ∧ acceleratedOrbit 15 23851 = 14330 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23851) = 3 ^ 9 * m + 14330 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23851.1, data_15_23851.2]

/-- Complete interval computation for depth 15, residue 23852. -/
theorem bounds_15_23852 : exactInterval 15 23852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23852 : oddCount 23852 15 = 4 ∧ acceleratedOrbit 15 23852 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23852) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23852.1, data_15_23852.2]

/-- Complete interval computation for depth 15, residue 23853. -/
theorem bounds_15_23853 : exactInterval 15 23853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23853 : oddCount 23853 15 = 4 ∧ acceleratedOrbit 15 23853 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23853) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23853.1, data_15_23853.2]

/-- Complete interval computation for depth 15, residue 23854. -/
theorem bounds_15_23854 : exactInterval 15 23854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23854 : oddCount 23854 15 = 4 ∧ acceleratedOrbit 15 23854 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23854) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23854.1, data_15_23854.2]

end Collatz.Research.PassageAtlas.Batch0728
