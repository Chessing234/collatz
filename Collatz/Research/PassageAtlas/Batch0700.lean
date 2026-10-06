import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0700

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22904. -/
theorem bounds_15_22904 : exactInterval 15 22904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22904 : oddCount 22904 15 = 8 ∧ acceleratedOrbit 15 22904 = 4589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22904) = 3 ^ 8 * m + 4589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22904.1, data_15_22904.2]

/-- Complete interval computation for depth 15, residue 22905. -/
theorem bounds_15_22905 : exactInterval 15 22905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22905 : oddCount 22905 15 = 11 ∧ acceleratedOrbit 15 22905 = 123839 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22905) = 3 ^ 11 * m + 123839 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22905.1, data_15_22905.2]

/-- Complete interval computation for depth 15, residue 22906. -/
theorem bounds_15_22906 : exactInterval 15 22906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22906 : oddCount 22906 15 = 8 ∧ acceleratedOrbit 15 22906 = 4589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22906) = 3 ^ 8 * m + 4589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22906.1, data_15_22906.2]

/-- Complete interval computation for depth 15, residue 22907. -/
theorem bounds_15_22907 : exactInterval 15 22907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22907 : oddCount 22907 15 = 7 ∧ acceleratedOrbit 15 22907 = 1529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22907) = 3 ^ 7 * m + 1529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22907.1, data_15_22907.2]

/-- Complete interval computation for depth 15, residue 22908. -/
theorem bounds_15_22908 : exactInterval 15 22908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22908 : oddCount 22908 15 = 8 ∧ acceleratedOrbit 15 22908 = 4589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22908) = 3 ^ 8 * m + 4589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22908.1, data_15_22908.2]

/-- Complete interval computation for depth 15, residue 22909. -/
theorem bounds_15_22909 : exactInterval 15 22909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22909 : oddCount 22909 15 = 8 ∧ acceleratedOrbit 15 22909 = 4589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22909) = 3 ^ 8 * m + 4589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22909.1, data_15_22909.2]

/-- Complete interval computation for depth 15, residue 22910. -/
theorem bounds_15_22910 : exactInterval 15 22910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22910 : oddCount 22910 15 = 9 ∧ acceleratedOrbit 15 22910 = 13763 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22910) = 3 ^ 9 * m + 13763 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22910.1, data_15_22910.2]

/-- Complete interval computation for depth 15, residue 22911. -/
theorem bounds_15_22911 : exactInterval 15 22911 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22911) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22911 : oddCount 22911 15 = 9 ∧ acceleratedOrbit 15 22911 = 13763 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22911) = 3 ^ 9 * m + 13763 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22911.1, data_15_22911.2]

/-- Complete interval computation for depth 15, residue 22912. -/
theorem bounds_15_22912 : exactInterval 15 22912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22912 : oddCount 22912 15 = 3 ∧ acceleratedOrbit 15 22912 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22912) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22912.1, data_15_22912.2]

/-- Complete interval computation for depth 15, residue 22913. -/
theorem bounds_15_22913 : exactInterval 15 22913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22913 : oddCount 22913 15 = 9 ∧ acceleratedOrbit 15 22913 = 13769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22913) = 3 ^ 9 * m + 13769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22913.1, data_15_22913.2]

/-- Complete interval computation for depth 15, residue 22914. -/
theorem bounds_15_22914 : exactInterval 15 22914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22914 : oddCount 22914 15 = 5 ∧ acceleratedOrbit 15 22914 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22914) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22914.1, data_15_22914.2]

/-- Complete interval computation for depth 15, residue 22915. -/
theorem bounds_15_22915 : exactInterval 15 22915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22915 : oddCount 22915 15 = 5 ∧ acceleratedOrbit 15 22915 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22915) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22915.1, data_15_22915.2]

/-- Complete interval computation for depth 15, residue 22916. -/
theorem bounds_15_22916 : exactInterval 15 22916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22916 : oddCount 22916 15 = 5 ∧ acceleratedOrbit 15 22916 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22916) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22916.1, data_15_22916.2]

/-- Complete interval computation for depth 15, residue 22917. -/
theorem bounds_15_22917 : exactInterval 15 22917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22917 : oddCount 22917 15 = 5 ∧ acceleratedOrbit 15 22917 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22917) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22917.1, data_15_22917.2]

/-- Complete interval computation for depth 15, residue 22918. -/
theorem bounds_15_22918 : exactInterval 15 22918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22918 : oddCount 22918 15 = 5 ∧ acceleratedOrbit 15 22918 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22918) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22918.1, data_15_22918.2]

/-- Complete interval computation for depth 15, residue 22919. -/
theorem bounds_15_22919 : exactInterval 15 22919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22919 : oddCount 22919 15 = 5 ∧ acceleratedOrbit 15 22919 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22919) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22919.1, data_15_22919.2]

/-- Complete interval computation for depth 15, residue 22920. -/
theorem bounds_15_22920 : exactInterval 15 22920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22920 : oddCount 22920 15 = 6 ∧ acceleratedOrbit 15 22920 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22920) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22920.1, data_15_22920.2]

/-- Complete interval computation for depth 15, residue 22921. -/
theorem bounds_15_22921 : exactInterval 15 22921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22921 : oddCount 22921 15 = 11 ∧ acceleratedOrbit 15 22921 = 123929 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22921) = 3 ^ 11 * m + 123929 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22921.1, data_15_22921.2]

/-- Complete interval computation for depth 15, residue 22922. -/
theorem bounds_15_22922 : exactInterval 15 22922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22922 : oddCount 22922 15 = 6 ∧ acceleratedOrbit 15 22922 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22922) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22922.1, data_15_22922.2]

/-- Complete interval computation for depth 15, residue 22923. -/
theorem bounds_15_22923 : exactInterval 15 22923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22923 : oddCount 22923 15 = 9 ∧ acceleratedOrbit 15 22923 = 13772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22923) = 3 ^ 9 * m + 13772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22923.1, data_15_22923.2]

/-- Complete interval computation for depth 15, residue 22924. -/
theorem bounds_15_22924 : exactInterval 15 22924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22924 : oddCount 22924 15 = 6 ∧ acceleratedOrbit 15 22924 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22924) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22924.1, data_15_22924.2]

/-- Complete interval computation for depth 15, residue 22925. -/
theorem bounds_15_22925 : exactInterval 15 22925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22925 : oddCount 22925 15 = 6 ∧ acceleratedOrbit 15 22925 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22925) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22925.1, data_15_22925.2]

/-- Complete interval computation for depth 15, residue 22926. -/
theorem bounds_15_22926 : exactInterval 15 22926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22926 : oddCount 22926 15 = 8 ∧ acceleratedOrbit 15 22926 = 4592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22926) = 3 ^ 8 * m + 4592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22926.1, data_15_22926.2]

/-- Complete interval computation for depth 15, residue 22927. -/
theorem bounds_15_22927 : exactInterval 15 22927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22927 : oddCount 22927 15 = 8 ∧ acceleratedOrbit 15 22927 = 4592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22927) = 3 ^ 8 * m + 4592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22927.1, data_15_22927.2]

/-- Complete interval computation for depth 15, residue 22928. -/
theorem bounds_15_22928 : exactInterval 15 22928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22928 : oddCount 22928 15 = 6 ∧ acceleratedOrbit 15 22928 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22928) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22928.1, data_15_22928.2]

/-- Complete interval computation for depth 15, residue 22929. -/
theorem bounds_15_22929 : exactInterval 15 22929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22929 : oddCount 22929 15 = 7 ∧ acceleratedOrbit 15 22929 = 1532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22929) = 3 ^ 7 * m + 1532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22929.1, data_15_22929.2]

/-- Complete interval computation for depth 15, residue 22930. -/
theorem bounds_15_22930 : exactInterval 15 22930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22930 : oddCount 22930 15 = 7 ∧ acceleratedOrbit 15 22930 = 1532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22930) = 3 ^ 7 * m + 1532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22930.1, data_15_22930.2]

/-- Complete interval computation for depth 15, residue 22931. -/
theorem bounds_15_22931 : exactInterval 15 22931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22931 : oddCount 22931 15 = 7 ∧ acceleratedOrbit 15 22931 = 1532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22931) = 3 ^ 7 * m + 1532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22931.1, data_15_22931.2]

/-- Complete interval computation for depth 15, residue 22932. -/
theorem bounds_15_22932 : exactInterval 15 22932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22932 : oddCount 22932 15 = 6 ∧ acceleratedOrbit 15 22932 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22932) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22932.1, data_15_22932.2]

/-- Complete interval computation for depth 15, residue 22933. -/
theorem bounds_15_22933 : exactInterval 15 22933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22933 : oddCount 22933 15 = 6 ∧ acceleratedOrbit 15 22933 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22933) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22933.1, data_15_22933.2]

/-- Complete interval computation for depth 15, residue 22934. -/
theorem bounds_15_22934 : exactInterval 15 22934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22934 : oddCount 22934 15 = 7 ∧ acceleratedOrbit 15 22934 = 1532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22934) = 3 ^ 7 * m + 1532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22934.1, data_15_22934.2]

/-- Complete interval computation for depth 15, residue 22935. -/
theorem bounds_15_22935 : exactInterval 15 22935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22935 : oddCount 22935 15 = 7 ∧ acceleratedOrbit 15 22935 = 1532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22935) = 3 ^ 7 * m + 1532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22935.1, data_15_22935.2]

/-- Complete interval computation for depth 15, residue 22936. -/
theorem bounds_15_22936 : exactInterval 15 22936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22936 : oddCount 22936 15 = 6 ∧ acceleratedOrbit 15 22936 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22936) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22936.1, data_15_22936.2]

end Collatz.Research.PassageAtlas.Batch0700
