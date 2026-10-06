import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0181

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5898. -/
theorem bounds_15_5898 : exactInterval 15 5898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5898 : oddCount 5898 15 = 9 ∧ acceleratedOrbit 15 5898 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5898) = 3 ^ 9 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5898.1, data_15_5898.2]

/-- Complete interval computation for depth 15, residue 5899. -/
theorem bounds_15_5899 : exactInterval 15 5899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5899 : oddCount 5899 15 = 7 ∧ acceleratedOrbit 15 5899 = 394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5899) = 3 ^ 7 * m + 394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5899.1, data_15_5899.2]

/-- Complete interval computation for depth 15, residue 5900. -/
theorem bounds_15_5900 : exactInterval 15 5900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5900 : oddCount 5900 15 = 9 ∧ acceleratedOrbit 15 5900 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5900) = 3 ^ 9 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5900.1, data_15_5900.2]

/-- Complete interval computation for depth 15, residue 5901. -/
theorem bounds_15_5901 : exactInterval 15 5901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5901 : oddCount 5901 15 = 9 ∧ acceleratedOrbit 15 5901 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5901) = 3 ^ 9 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5901.1, data_15_5901.2]

/-- Complete interval computation for depth 15, residue 5902. -/
theorem bounds_15_5902 : exactInterval 15 5902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5902 : oddCount 5902 15 = 7 ∧ acceleratedOrbit 15 5902 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5902) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5902.1, data_15_5902.2]

/-- Complete interval computation for depth 15, residue 5903. -/
theorem bounds_15_5903 : exactInterval 15 5903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5903 : oddCount 5903 15 = 7 ∧ acceleratedOrbit 15 5903 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5903) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5903.1, data_15_5903.2]

/-- Complete interval computation for depth 15, residue 5904. -/
theorem bounds_15_5904 : exactInterval 15 5904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5904 : oddCount 5904 15 = 3 ∧ acceleratedOrbit 15 5904 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5904) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5904.1, data_15_5904.2]

/-- Complete interval computation for depth 15, residue 5905. -/
theorem bounds_15_5905 : exactInterval 15 5905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5905 : oddCount 5905 15 = 9 ∧ acceleratedOrbit 15 5905 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5905) = 3 ^ 9 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5905.1, data_15_5905.2]

/-- Complete interval computation for depth 15, residue 5906. -/
theorem bounds_15_5906 : exactInterval 15 5906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5906 : oddCount 5906 15 = 10 ∧ acceleratedOrbit 15 5906 = 10651 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5906) = 3 ^ 10 * m + 10651 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5906.1, data_15_5906.2]

/-- Complete interval computation for depth 15, residue 5907. -/
theorem bounds_15_5907 : exactInterval 15 5907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5907 : oddCount 5907 15 = 10 ∧ acceleratedOrbit 15 5907 = 10651 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5907) = 3 ^ 10 * m + 10651 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5907.1, data_15_5907.2]

/-- Complete interval computation for depth 15, residue 5908. -/
theorem bounds_15_5908 : exactInterval 15 5908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5908 : oddCount 5908 15 = 3 ∧ acceleratedOrbit 15 5908 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5908) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5908.1, data_15_5908.2]

/-- Complete interval computation for depth 15, residue 5909. -/
theorem bounds_15_5909 : exactInterval 15 5909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5909 : oddCount 5909 15 = 3 ∧ acceleratedOrbit 15 5909 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5909) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5909.1, data_15_5909.2]

/-- Complete interval computation for depth 15, residue 5910. -/
theorem bounds_15_5910 : exactInterval 15 5910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5910 : oddCount 5910 15 = 9 ∧ acceleratedOrbit 15 5910 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5910) = 3 ^ 9 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5910.1, data_15_5910.2]

/-- Complete interval computation for depth 15, residue 5911. -/
theorem bounds_15_5911 : exactInterval 15 5911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5911 : oddCount 5911 15 = 9 ∧ acceleratedOrbit 15 5911 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5911) = 3 ^ 9 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5911.1, data_15_5911.2]

/-- Complete interval computation for depth 15, residue 5912. -/
theorem bounds_15_5912 : exactInterval 15 5912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5912 : oddCount 5912 15 = 3 ∧ acceleratedOrbit 15 5912 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5912) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5912.1, data_15_5912.2]

/-- Complete interval computation for depth 15, residue 5913. -/
theorem bounds_15_5913 : exactInterval 15 5913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5913 : oddCount 5913 15 = 11 ∧ acceleratedOrbit 15 5913 = 31985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5913) = 3 ^ 11 * m + 31985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5913.1, data_15_5913.2]

/-- Complete interval computation for depth 15, residue 5914. -/
theorem bounds_15_5914 : exactInterval 15 5914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5914 : oddCount 5914 15 = 3 ∧ acceleratedOrbit 15 5914 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5914) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5914.1, data_15_5914.2]

/-- Complete interval computation for depth 15, residue 5915. -/
theorem bounds_15_5915 : exactInterval 15 5915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5915 : oddCount 5915 15 = 13 ∧ acceleratedOrbit 15 5915 = 287864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5915) = 3 ^ 13 * m + 287864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5915.1, data_15_5915.2]

/-- Complete interval computation for depth 15, residue 5916. -/
theorem bounds_15_5916 : exactInterval 15 5916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5916 : oddCount 5916 15 = 8 ∧ acceleratedOrbit 15 5916 = 1187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5916) = 3 ^ 8 * m + 1187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5916.1, data_15_5916.2]

/-- Complete interval computation for depth 15, residue 5917. -/
theorem bounds_15_5917 : exactInterval 15 5917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5917 : oddCount 5917 15 = 8 ∧ acceleratedOrbit 15 5917 = 1187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5917) = 3 ^ 8 * m + 1187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5917.1, data_15_5917.2]

/-- Complete interval computation for depth 15, residue 5918. -/
theorem bounds_15_5918 : exactInterval 15 5918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5918 : oddCount 5918 15 = 8 ∧ acceleratedOrbit 15 5918 = 1187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5918) = 3 ^ 8 * m + 1187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5918.1, data_15_5918.2]

/-- Complete interval computation for depth 15, residue 5919. -/
theorem bounds_15_5919 : exactInterval 15 5919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5919 : oddCount 5919 15 = 9 ∧ acceleratedOrbit 15 5919 = 3557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5919) = 3 ^ 9 * m + 3557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5919.1, data_15_5919.2]

/-- Complete interval computation for depth 15, residue 5920. -/
theorem bounds_15_5920 : exactInterval 15 5920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5920 : oddCount 5920 15 = 6 ∧ acceleratedOrbit 15 5920 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5920) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5920.1, data_15_5920.2]

/-- Complete interval computation for depth 15, residue 5921. -/
theorem bounds_15_5921 : exactInterval 15 5921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5921 : oddCount 5921 15 = 9 ∧ acceleratedOrbit 15 5921 = 3563 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5921) = 3 ^ 9 * m + 3563 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5921.1, data_15_5921.2]

/-- Complete interval computation for depth 15, residue 5922. -/
theorem bounds_15_5922 : exactInterval 15 5922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5922 : oddCount 5922 15 = 5 ∧ acceleratedOrbit 15 5922 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5922) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5922.1, data_15_5922.2]

/-- Complete interval computation for depth 15, residue 5923. -/
theorem bounds_15_5923 : exactInterval 15 5923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5923 : oddCount 5923 15 = 5 ∧ acceleratedOrbit 15 5923 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5923) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5923.1, data_15_5923.2]

/-- Complete interval computation for depth 15, residue 5924. -/
theorem bounds_15_5924 : exactInterval 15 5924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5924 : oddCount 5924 15 = 5 ∧ acceleratedOrbit 15 5924 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5924) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5924.1, data_15_5924.2]

/-- Complete interval computation for depth 15, residue 5925. -/
theorem bounds_15_5925 : exactInterval 15 5925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5925 : oddCount 5925 15 = 5 ∧ acceleratedOrbit 15 5925 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5925) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5925.1, data_15_5925.2]

/-- Complete interval computation for depth 15, residue 5926. -/
theorem bounds_15_5926 : exactInterval 15 5926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5926 : oddCount 5926 15 = 5 ∧ acceleratedOrbit 15 5926 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5926) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5926.1, data_15_5926.2]

/-- Complete interval computation for depth 15, residue 5927. -/
theorem bounds_15_5927 : exactInterval 15 5927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5927 : oddCount 5927 15 = 10 ∧ acceleratedOrbit 15 5927 = 10685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5927) = 3 ^ 10 * m + 10685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5927.1, data_15_5927.2]

/-- Complete interval computation for depth 15, residue 5928. -/
theorem bounds_15_5928 : exactInterval 15 5928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5928 : oddCount 5928 15 = 6 ∧ acceleratedOrbit 15 5928 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5928) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5928.1, data_15_5928.2]

/-- Complete interval computation for depth 15, residue 5929. -/
theorem bounds_15_5929 : exactInterval 15 5929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5929 : oddCount 5929 15 = 10 ∧ acceleratedOrbit 15 5929 = 10691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5929) = 3 ^ 10 * m + 10691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5929.1, data_15_5929.2]

/-- Complete interval computation for depth 15, residue 5930. -/
theorem bounds_15_5930 : exactInterval 15 5930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5930 : oddCount 5930 15 = 6 ∧ acceleratedOrbit 15 5930 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5930) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5930.1, data_15_5930.2]

end Collatz.Research.PassageAtlas.Batch0181
