import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0242

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7897. -/
theorem bounds_15_7897 : exactInterval 15 7897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7897 : oddCount 7897 15 = 6 ∧ acceleratedOrbit 15 7897 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7897) = 3 ^ 6 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7897.1, data_15_7897.2]

/-- Complete interval computation for depth 15, residue 7898. -/
theorem bounds_15_7898 : exactInterval 15 7898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7898 : oddCount 7898 15 = 6 ∧ acceleratedOrbit 15 7898 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7898) = 3 ^ 6 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7898.1, data_15_7898.2]

/-- Complete interval computation for depth 15, residue 7899. -/
theorem bounds_15_7899 : exactInterval 15 7899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7899 : oddCount 7899 15 = 8 ∧ acceleratedOrbit 15 7899 = 1582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7899) = 3 ^ 8 * m + 1582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7899.1, data_15_7899.2]

/-- Complete interval computation for depth 15, residue 7900. -/
theorem bounds_15_7900 : exactInterval 15 7900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7900 : oddCount 7900 15 = 6 ∧ acceleratedOrbit 15 7900 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7900) = 3 ^ 6 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7900.1, data_15_7900.2]

/-- Complete interval computation for depth 15, residue 7901. -/
theorem bounds_15_7901 : exactInterval 15 7901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7901 : oddCount 7901 15 = 6 ∧ acceleratedOrbit 15 7901 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7901) = 3 ^ 6 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7901.1, data_15_7901.2]

/-- Complete interval computation for depth 15, residue 7902. -/
theorem bounds_15_7902 : exactInterval 15 7902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7902 : oddCount 7902 15 = 10 ∧ acceleratedOrbit 15 7902 = 14246 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7902) = 3 ^ 10 * m + 14246 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7902.1, data_15_7902.2]

/-- Complete interval computation for depth 15, residue 7903. -/
theorem bounds_15_7903 : exactInterval 15 7903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7903 : oddCount 7903 15 = 10 ∧ acceleratedOrbit 15 7903 = 14246 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7903) = 3 ^ 10 * m + 14246 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7903.1, data_15_7903.2]

/-- Complete interval computation for depth 15, residue 7904. -/
theorem bounds_15_7904 : exactInterval 15 7904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7904 : oddCount 7904 15 = 5 ∧ acceleratedOrbit 15 7904 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7904) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7904.1, data_15_7904.2]

/-- Complete interval computation for depth 15, residue 7905. -/
theorem bounds_15_7905 : exactInterval 15 7905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7905 : oddCount 7905 15 = 9 ∧ acceleratedOrbit 15 7905 = 4751 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7905) = 3 ^ 9 * m + 4751 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7905.1, data_15_7905.2]

/-- Complete interval computation for depth 15, residue 7906. -/
theorem bounds_15_7906 : exactInterval 15 7906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7906 : oddCount 7906 15 = 5 ∧ acceleratedOrbit 15 7906 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7906) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7906.1, data_15_7906.2]

/-- Complete interval computation for depth 15, residue 7907. -/
theorem bounds_15_7907 : exactInterval 15 7907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7907 : oddCount 7907 15 = 5 ∧ acceleratedOrbit 15 7907 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7907) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7907.1, data_15_7907.2]

/-- Complete interval computation for depth 15, residue 7908. -/
theorem bounds_15_7908 : exactInterval 15 7908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7908 : oddCount 7908 15 = 7 ∧ acceleratedOrbit 15 7908 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7908) = 3 ^ 7 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7908.1, data_15_7908.2]

/-- Complete interval computation for depth 15, residue 7909. -/
theorem bounds_15_7909 : exactInterval 15 7909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7909 : oddCount 7909 15 = 7 ∧ acceleratedOrbit 15 7909 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7909) = 3 ^ 7 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7909.1, data_15_7909.2]

/-- Complete interval computation for depth 15, residue 7910. -/
theorem bounds_15_7910 : exactInterval 15 7910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7910 : oddCount 7910 15 = 7 ∧ acceleratedOrbit 15 7910 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7910) = 3 ^ 7 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7910.1, data_15_7910.2]

/-- Complete interval computation for depth 15, residue 7911. -/
theorem bounds_15_7911 : exactInterval 15 7911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7911 : oddCount 7911 15 = 9 ∧ acceleratedOrbit 15 7911 = 4753 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7911) = 3 ^ 9 * m + 4753 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7911.1, data_15_7911.2]

/-- Complete interval computation for depth 15, residue 7912. -/
theorem bounds_15_7912 : exactInterval 15 7912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7912 : oddCount 7912 15 = 5 ∧ acceleratedOrbit 15 7912 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7912) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7912.1, data_15_7912.2]

/-- Complete interval computation for depth 15, residue 7913. -/
theorem bounds_15_7913 : exactInterval 15 7913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7913 : oddCount 7913 15 = 8 ∧ acceleratedOrbit 15 7913 = 1585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7913) = 3 ^ 8 * m + 1585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7913.1, data_15_7913.2]

/-- Complete interval computation for depth 15, residue 7914. -/
theorem bounds_15_7914 : exactInterval 15 7914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7914 : oddCount 7914 15 = 5 ∧ acceleratedOrbit 15 7914 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7914) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7914.1, data_15_7914.2]

/-- Complete interval computation for depth 15, residue 7915. -/
theorem bounds_15_7915 : exactInterval 15 7915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7915 : oddCount 7915 15 = 8 ∧ acceleratedOrbit 15 7915 = 1586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7915) = 3 ^ 8 * m + 1586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7915.1, data_15_7915.2]

/-- Complete interval computation for depth 15, residue 7916. -/
theorem bounds_15_7916 : exactInterval 15 7916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7916 : oddCount 7916 15 = 7 ∧ acceleratedOrbit 15 7916 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7916) = 3 ^ 7 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7916.1, data_15_7916.2]

/-- Complete interval computation for depth 15, residue 7917. -/
theorem bounds_15_7917 : exactInterval 15 7917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7917 : oddCount 7917 15 = 7 ∧ acceleratedOrbit 15 7917 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7917) = 3 ^ 7 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7917.1, data_15_7917.2]

/-- Complete interval computation for depth 15, residue 7918. -/
theorem bounds_15_7918 : exactInterval 15 7918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7918 : oddCount 7918 15 = 7 ∧ acceleratedOrbit 15 7918 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7918) = 3 ^ 7 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7918.1, data_15_7918.2]

/-- Complete interval computation for depth 15, residue 7919. -/
theorem bounds_15_7919 : exactInterval 15 7919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7919 : oddCount 7919 15 = 10 ∧ acceleratedOrbit 15 7919 = 14273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7919) = 3 ^ 10 * m + 14273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7919.1, data_15_7919.2]

/-- Complete interval computation for depth 15, residue 7920. -/
theorem bounds_15_7920 : exactInterval 15 7920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7920 : oddCount 7920 15 = 9 ∧ acceleratedOrbit 15 7920 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7920) = 3 ^ 9 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7920.1, data_15_7920.2]

/-- Complete interval computation for depth 15, residue 7921. -/
theorem bounds_15_7921 : exactInterval 15 7921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7921 : oddCount 7921 15 = 5 ∧ acceleratedOrbit 15 7921 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7921) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7921.1, data_15_7921.2]

/-- Complete interval computation for depth 15, residue 7922. -/
theorem bounds_15_7922 : exactInterval 15 7922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7922 : oddCount 7922 15 = 7 ∧ acceleratedOrbit 15 7922 = 529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7922) = 3 ^ 7 * m + 529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7922.1, data_15_7922.2]

/-- Complete interval computation for depth 15, residue 7923. -/
theorem bounds_15_7923 : exactInterval 15 7923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7923 : oddCount 7923 15 = 7 ∧ acceleratedOrbit 15 7923 = 529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7923) = 3 ^ 7 * m + 529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7923.1, data_15_7923.2]

/-- Complete interval computation for depth 15, residue 7924. -/
theorem bounds_15_7924 : exactInterval 15 7924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7924 : oddCount 7924 15 = 9 ∧ acceleratedOrbit 15 7924 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7924) = 3 ^ 9 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7924.1, data_15_7924.2]

/-- Complete interval computation for depth 15, residue 7925. -/
theorem bounds_15_7925 : exactInterval 15 7925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7925 : oddCount 7925 15 = 9 ∧ acceleratedOrbit 15 7925 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7925) = 3 ^ 9 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7925.1, data_15_7925.2]

/-- Complete interval computation for depth 15, residue 7926. -/
theorem bounds_15_7926 : exactInterval 15 7926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7926 : oddCount 7926 15 = 8 ∧ acceleratedOrbit 15 7926 = 1588 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7926) = 3 ^ 8 * m + 1588 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7926.1, data_15_7926.2]

/-- Complete interval computation for depth 15, residue 7927. -/
theorem bounds_15_7927 : exactInterval 15 7927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7927 : oddCount 7927 15 = 8 ∧ acceleratedOrbit 15 7927 = 1588 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7927) = 3 ^ 8 * m + 1588 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7927.1, data_15_7927.2]

/-- Complete interval computation for depth 15, residue 7928. -/
theorem bounds_15_7928 : exactInterval 15 7928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7928 : oddCount 7928 15 = 9 ∧ acceleratedOrbit 15 7928 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7928) = 3 ^ 9 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7928.1, data_15_7928.2]

end Collatz.Research.PassageAtlas.Batch0242
