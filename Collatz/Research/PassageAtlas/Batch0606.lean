import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0606

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19824. -/
theorem bounds_15_19824 : exactInterval 15 19824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19824 : oddCount 19824 15 = 6 ∧ acceleratedOrbit 15 19824 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19824) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19824.1, data_15_19824.2]

/-- Complete interval computation for depth 15, residue 19825. -/
theorem bounds_15_19825 : exactInterval 15 19825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19825 : oddCount 19825 15 = 6 ∧ acceleratedOrbit 15 19825 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19825) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19825.1, data_15_19825.2]

/-- Complete interval computation for depth 15, residue 19826. -/
theorem bounds_15_19826 : exactInterval 15 19826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19826 : oddCount 19826 15 = 7 ∧ acceleratedOrbit 15 19826 = 1324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19826) = 3 ^ 7 * m + 1324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19826.1, data_15_19826.2]

/-- Complete interval computation for depth 15, residue 19827. -/
theorem bounds_15_19827 : exactInterval 15 19827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19827 : oddCount 19827 15 = 7 ∧ acceleratedOrbit 15 19827 = 1324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19827) = 3 ^ 7 * m + 1324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19827.1, data_15_19827.2]

/-- Complete interval computation for depth 15, residue 19828. -/
theorem bounds_15_19828 : exactInterval 15 19828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19828 : oddCount 19828 15 = 6 ∧ acceleratedOrbit 15 19828 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19828) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19828.1, data_15_19828.2]

/-- Complete interval computation for depth 15, residue 19829. -/
theorem bounds_15_19829 : exactInterval 15 19829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19829 : oddCount 19829 15 = 6 ∧ acceleratedOrbit 15 19829 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19829) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19829.1, data_15_19829.2]

/-- Complete interval computation for depth 15, residue 19830. -/
theorem bounds_15_19830 : exactInterval 15 19830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19830 : oddCount 19830 15 = 7 ∧ acceleratedOrbit 15 19830 = 1324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19830) = 3 ^ 7 * m + 1324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19830.1, data_15_19830.2]

/-- Complete interval computation for depth 15, residue 19831. -/
theorem bounds_15_19831 : exactInterval 15 19831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19831 : oddCount 19831 15 = 7 ∧ acceleratedOrbit 15 19831 = 1324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19831) = 3 ^ 7 * m + 1324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19831.1, data_15_19831.2]

/-- Complete interval computation for depth 15, residue 19832. -/
theorem bounds_15_19832 : exactInterval 15 19832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19832 : oddCount 19832 15 = 7 ∧ acceleratedOrbit 15 19832 = 1325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19832) = 3 ^ 7 * m + 1325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19832.1, data_15_19832.2]

/-- Complete interval computation for depth 15, residue 19833. -/
theorem bounds_15_19833 : exactInterval 15 19833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19833 : oddCount 19833 15 = 9 ∧ acceleratedOrbit 15 19833 = 11915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19833) = 3 ^ 9 * m + 11915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19833.1, data_15_19833.2]

/-- Complete interval computation for depth 15, residue 19834. -/
theorem bounds_15_19834 : exactInterval 15 19834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19834 : oddCount 19834 15 = 7 ∧ acceleratedOrbit 15 19834 = 1325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19834) = 3 ^ 7 * m + 1325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19834.1, data_15_19834.2]

/-- Complete interval computation for depth 15, residue 19835. -/
theorem bounds_15_19835 : exactInterval 15 19835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19835 : oddCount 19835 15 = 7 ∧ acceleratedOrbit 15 19835 = 1324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19835) = 3 ^ 7 * m + 1324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19835.1, data_15_19835.2]

/-- Complete interval computation for depth 15, residue 19836. -/
theorem bounds_15_19836 : exactInterval 15 19836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19836 : oddCount 19836 15 = 7 ∧ acceleratedOrbit 15 19836 = 1325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19836) = 3 ^ 7 * m + 1325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19836.1, data_15_19836.2]

/-- Complete interval computation for depth 15, residue 19837. -/
theorem bounds_15_19837 : exactInterval 15 19837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19837 : oddCount 19837 15 = 7 ∧ acceleratedOrbit 15 19837 = 1325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19837) = 3 ^ 7 * m + 1325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19837.1, data_15_19837.2]

/-- Complete interval computation for depth 15, residue 19838. -/
theorem bounds_15_19838 : exactInterval 15 19838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19838 : oddCount 19838 15 = 9 ∧ acceleratedOrbit 15 19838 = 11918 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19838) = 3 ^ 9 * m + 11918 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19838.1, data_15_19838.2]

/-- Complete interval computation for depth 15, residue 19839. -/
theorem bounds_15_19839 : exactInterval 15 19839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19839 : oddCount 19839 15 = 9 ∧ acceleratedOrbit 15 19839 = 11918 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19839) = 3 ^ 9 * m + 11918 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19839.1, data_15_19839.2]

/-- Complete interval computation for depth 15, residue 19840. -/
theorem bounds_15_19840 : exactInterval 15 19840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19840 : oddCount 19840 15 = 6 ∧ acceleratedOrbit 15 19840 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19840) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19840.1, data_15_19840.2]

/-- Complete interval computation for depth 15, residue 19841. -/
theorem bounds_15_19841 : exactInterval 15 19841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19841 : oddCount 19841 15 = 7 ∧ acceleratedOrbit 15 19841 = 1325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19841) = 3 ^ 7 * m + 1325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19841.1, data_15_19841.2]

/-- Complete interval computation for depth 15, residue 19842. -/
theorem bounds_15_19842 : exactInterval 15 19842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19842 : oddCount 19842 15 = 6 ∧ acceleratedOrbit 15 19842 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19842) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19842.1, data_15_19842.2]

/-- Complete interval computation for depth 15, residue 19843. -/
theorem bounds_15_19843 : exactInterval 15 19843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19843 : oddCount 19843 15 = 6 ∧ acceleratedOrbit 15 19843 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19843) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19843.1, data_15_19843.2]

/-- Complete interval computation for depth 15, residue 19844. -/
theorem bounds_15_19844 : exactInterval 15 19844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19844 : oddCount 19844 15 = 9 ∧ acceleratedOrbit 15 19844 = 11927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19844) = 3 ^ 9 * m + 11927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19844.1, data_15_19844.2]

/-- Complete interval computation for depth 15, residue 19845. -/
theorem bounds_15_19845 : exactInterval 15 19845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19845 : oddCount 19845 15 = 9 ∧ acceleratedOrbit 15 19845 = 11927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19845) = 3 ^ 9 * m + 11927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19845.1, data_15_19845.2]

/-- Complete interval computation for depth 15, residue 19846. -/
theorem bounds_15_19846 : exactInterval 15 19846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19846 : oddCount 19846 15 = 9 ∧ acceleratedOrbit 15 19846 = 11927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19846) = 3 ^ 9 * m + 11927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19846.1, data_15_19846.2]

/-- Complete interval computation for depth 15, residue 19847. -/
theorem bounds_15_19847 : exactInterval 15 19847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19847 : oddCount 19847 15 = 6 ∧ acceleratedOrbit 15 19847 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19847) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19847.1, data_15_19847.2]

/-- Complete interval computation for depth 15, residue 19848. -/
theorem bounds_15_19848 : exactInterval 15 19848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19848 : oddCount 19848 15 = 5 ∧ acceleratedOrbit 15 19848 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19848) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19848.1, data_15_19848.2]

/-- Complete interval computation for depth 15, residue 19849. -/
theorem bounds_15_19849 : exactInterval 15 19849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19849 : oddCount 19849 15 = 7 ∧ acceleratedOrbit 15 19849 = 1325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19849) = 3 ^ 7 * m + 1325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19849.1, data_15_19849.2]

/-- Complete interval computation for depth 15, residue 19850. -/
theorem bounds_15_19850 : exactInterval 15 19850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19850 : oddCount 19850 15 = 5 ∧ acceleratedOrbit 15 19850 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19850) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19850.1, data_15_19850.2]

/-- Complete interval computation for depth 15, residue 19851. -/
theorem bounds_15_19851 : exactInterval 15 19851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19851 : oddCount 19851 15 = 9 ∧ acceleratedOrbit 15 19851 = 11927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19851) = 3 ^ 9 * m + 11927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19851.1, data_15_19851.2]

/-- Complete interval computation for depth 15, residue 19852. -/
theorem bounds_15_19852 : exactInterval 15 19852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19852 : oddCount 19852 15 = 5 ∧ acceleratedOrbit 15 19852 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19852) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19852.1, data_15_19852.2]

/-- Complete interval computation for depth 15, residue 19853. -/
theorem bounds_15_19853 : exactInterval 15 19853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19853 : oddCount 19853 15 = 5 ∧ acceleratedOrbit 15 19853 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19853) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19853.1, data_15_19853.2]

/-- Complete interval computation for depth 15, residue 19854. -/
theorem bounds_15_19854 : exactInterval 15 19854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19854 : oddCount 19854 15 = 6 ∧ acceleratedOrbit 15 19854 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19854) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19854.1, data_15_19854.2]

/-- Complete interval computation for depth 15, residue 19855. -/
theorem bounds_15_19855 : exactInterval 15 19855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19855 : oddCount 19855 15 = 6 ∧ acceleratedOrbit 15 19855 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19855) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19855.1, data_15_19855.2]

/-- Complete interval computation for depth 15, residue 19856. -/
theorem bounds_15_19856 : exactInterval 15 19856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19856 : oddCount 19856 15 = 5 ∧ acceleratedOrbit 15 19856 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19856) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19856.1, data_15_19856.2]

end Collatz.Research.PassageAtlas.Batch0606
