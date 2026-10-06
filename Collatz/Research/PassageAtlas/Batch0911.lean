import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0911

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29818. -/
theorem bounds_15_29818 : exactInterval 15 29818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29818 : oddCount 29818 15 = 7 ∧ acceleratedOrbit 15 29818 = 1991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29818) = 3 ^ 7 * m + 1991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29818.1, data_15_29818.2]

/-- Complete interval computation for depth 15, residue 29819. -/
theorem bounds_15_29819 : exactInterval 15 29819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29819 : oddCount 29819 15 = 9 ∧ acceleratedOrbit 15 29819 = 17914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29819) = 3 ^ 9 * m + 17914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29819.1, data_15_29819.2]

/-- Complete interval computation for depth 15, residue 29820. -/
theorem bounds_15_29820 : exactInterval 15 29820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29820 : oddCount 29820 15 = 7 ∧ acceleratedOrbit 15 29820 = 1991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29820) = 3 ^ 7 * m + 1991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29820.1, data_15_29820.2]

/-- Complete interval computation for depth 15, residue 29821. -/
theorem bounds_15_29821 : exactInterval 15 29821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29821 : oddCount 29821 15 = 7 ∧ acceleratedOrbit 15 29821 = 1991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29821) = 3 ^ 7 * m + 1991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29821.1, data_15_29821.2]

/-- Complete interval computation for depth 15, residue 29822. -/
theorem bounds_15_29822 : exactInterval 15 29822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29822 : oddCount 29822 15 = 7 ∧ acceleratedOrbit 15 29822 = 1991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29822) = 3 ^ 7 * m + 1991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29822.1, data_15_29822.2]

/-- Complete interval computation for depth 15, residue 29823. -/
theorem bounds_15_29823 : exactInterval 15 29823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29823 : oddCount 29823 15 = 10 ∧ acceleratedOrbit 15 29823 = 53744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29823) = 3 ^ 10 * m + 53744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29823.1, data_15_29823.2]

/-- Complete interval computation for depth 15, residue 29824. -/
theorem bounds_15_29824 : exactInterval 15 29824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29824 : oddCount 29824 15 = 6 ∧ acceleratedOrbit 15 29824 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29824) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29824.1, data_15_29824.2]

/-- Complete interval computation for depth 15, residue 29825. -/
theorem bounds_15_29825 : exactInterval 15 29825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29825 : oddCount 29825 15 = 9 ∧ acceleratedOrbit 15 29825 = 17918 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29825) = 3 ^ 9 * m + 17918 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29825.1, data_15_29825.2]

/-- Complete interval computation for depth 15, residue 29826. -/
theorem bounds_15_29826 : exactInterval 15 29826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29826 : oddCount 29826 15 = 6 ∧ acceleratedOrbit 15 29826 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29826) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29826.1, data_15_29826.2]

/-- Complete interval computation for depth 15, residue 29827. -/
theorem bounds_15_29827 : exactInterval 15 29827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29827 : oddCount 29827 15 = 6 ∧ acceleratedOrbit 15 29827 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29827) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29827.1, data_15_29827.2]

/-- Complete interval computation for depth 15, residue 29828. -/
theorem bounds_15_29828 : exactInterval 15 29828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29828 : oddCount 29828 15 = 6 ∧ acceleratedOrbit 15 29828 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29828) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29828.1, data_15_29828.2]

/-- Complete interval computation for depth 15, residue 29829. -/
theorem bounds_15_29829 : exactInterval 15 29829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29829 : oddCount 29829 15 = 6 ∧ acceleratedOrbit 15 29829 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29829) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29829.1, data_15_29829.2]

/-- Complete interval computation for depth 15, residue 29830. -/
theorem bounds_15_29830 : exactInterval 15 29830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29830 : oddCount 29830 15 = 6 ∧ acceleratedOrbit 15 29830 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29830) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29830.1, data_15_29830.2]

/-- Complete interval computation for depth 15, residue 29831. -/
theorem bounds_15_29831 : exactInterval 15 29831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29831 : oddCount 29831 15 = 9 ∧ acceleratedOrbit 15 29831 = 17921 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29831) = 3 ^ 9 * m + 17921 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29831.1, data_15_29831.2]

/-- Complete interval computation for depth 15, residue 29832. -/
theorem bounds_15_29832 : exactInterval 15 29832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29832 : oddCount 29832 15 = 6 ∧ acceleratedOrbit 15 29832 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29832) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29832.1, data_15_29832.2]

/-- Complete interval computation for depth 15, residue 29833. -/
theorem bounds_15_29833 : exactInterval 15 29833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29833 : oddCount 29833 15 = 11 ∧ acceleratedOrbit 15 29833 = 161291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29833) = 3 ^ 11 * m + 161291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29833.1, data_15_29833.2]

/-- Complete interval computation for depth 15, residue 29834. -/
theorem bounds_15_29834 : exactInterval 15 29834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29834 : oddCount 29834 15 = 6 ∧ acceleratedOrbit 15 29834 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29834) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29834.1, data_15_29834.2]

/-- Complete interval computation for depth 15, residue 29835. -/
theorem bounds_15_29835 : exactInterval 15 29835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29835 : oddCount 29835 15 = 8 ∧ acceleratedOrbit 15 29835 = 5975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29835) = 3 ^ 8 * m + 5975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29835.1, data_15_29835.2]

/-- Complete interval computation for depth 15, residue 29836. -/
theorem bounds_15_29836 : exactInterval 15 29836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29836 : oddCount 29836 15 = 6 ∧ acceleratedOrbit 15 29836 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29836) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29836.1, data_15_29836.2]

/-- Complete interval computation for depth 15, residue 29837. -/
theorem bounds_15_29837 : exactInterval 15 29837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29837 : oddCount 29837 15 = 6 ∧ acceleratedOrbit 15 29837 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29837) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29837.1, data_15_29837.2]

/-- Complete interval computation for depth 15, residue 29838. -/
theorem bounds_15_29838 : exactInterval 15 29838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29838 : oddCount 29838 15 = 9 ∧ acceleratedOrbit 15 29838 = 17927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29838) = 3 ^ 9 * m + 17927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29838.1, data_15_29838.2]

/-- Complete interval computation for depth 15, residue 29839. -/
theorem bounds_15_29839 : exactInterval 15 29839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29839 : oddCount 29839 15 = 9 ∧ acceleratedOrbit 15 29839 = 17927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29839) = 3 ^ 9 * m + 17927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29839.1, data_15_29839.2]

/-- Complete interval computation for depth 15, residue 29840. -/
theorem bounds_15_29840 : exactInterval 15 29840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29840 : oddCount 29840 15 = 6 ∧ acceleratedOrbit 15 29840 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29840) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29840.1, data_15_29840.2]

/-- Complete interval computation for depth 15, residue 29841. -/
theorem bounds_15_29841 : exactInterval 15 29841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29841 : oddCount 29841 15 = 6 ∧ acceleratedOrbit 15 29841 = 664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29841) = 3 ^ 6 * m + 664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29841.1, data_15_29841.2]

/-- Complete interval computation for depth 15, residue 29842. -/
theorem bounds_15_29842 : exactInterval 15 29842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29842 : oddCount 29842 15 = 6 ∧ acceleratedOrbit 15 29842 = 664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29842) = 3 ^ 6 * m + 664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29842.1, data_15_29842.2]

/-- Complete interval computation for depth 15, residue 29843. -/
theorem bounds_15_29843 : exactInterval 15 29843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29843 : oddCount 29843 15 = 6 ∧ acceleratedOrbit 15 29843 = 664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29843) = 3 ^ 6 * m + 664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29843.1, data_15_29843.2]

/-- Complete interval computation for depth 15, residue 29844. -/
theorem bounds_15_29844 : exactInterval 15 29844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29844 : oddCount 29844 15 = 6 ∧ acceleratedOrbit 15 29844 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29844) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29844.1, data_15_29844.2]

/-- Complete interval computation for depth 15, residue 29845. -/
theorem bounds_15_29845 : exactInterval 15 29845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29845 : oddCount 29845 15 = 6 ∧ acceleratedOrbit 15 29845 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29845) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29845.1, data_15_29845.2]

/-- Complete interval computation for depth 15, residue 29846. -/
theorem bounds_15_29846 : exactInterval 15 29846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29846 : oddCount 29846 15 = 6 ∧ acceleratedOrbit 15 29846 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29846) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29846.1, data_15_29846.2]

/-- Complete interval computation for depth 15, residue 29847. -/
theorem bounds_15_29847 : exactInterval 15 29847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29847 : oddCount 29847 15 = 6 ∧ acceleratedOrbit 15 29847 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29847) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29847.1, data_15_29847.2]

/-- Complete interval computation for depth 15, residue 29848. -/
theorem bounds_15_29848 : exactInterval 15 29848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29848 : oddCount 29848 15 = 6 ∧ acceleratedOrbit 15 29848 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29848) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29848.1, data_15_29848.2]

/-- Complete interval computation for depth 15, residue 29849. -/
theorem bounds_15_29849 : exactInterval 15 29849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29849 : oddCount 29849 15 = 7 ∧ acceleratedOrbit 15 29849 = 1993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29849) = 3 ^ 7 * m + 1993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29849.1, data_15_29849.2]

/-- Complete interval computation for depth 15, residue 29850. -/
theorem bounds_15_29850 : exactInterval 15 29850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29850 : oddCount 29850 15 = 6 ∧ acceleratedOrbit 15 29850 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29850) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29850.1, data_15_29850.2]

end Collatz.Research.PassageAtlas.Batch0911
