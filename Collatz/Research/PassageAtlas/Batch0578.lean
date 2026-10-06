import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0578

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18907. -/
theorem bounds_15_18907 : exactInterval 15 18907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18907 : oddCount 18907 15 = 9 ∧ acceleratedOrbit 15 18907 = 11360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18907) = 3 ^ 9 * m + 11360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18907.1, data_15_18907.2]

/-- Complete interval computation for depth 15, residue 18908. -/
theorem bounds_15_18908 : exactInterval 15 18908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18908 : oddCount 18908 15 = 6 ∧ acceleratedOrbit 15 18908 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18908) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18908.1, data_15_18908.2]

/-- Complete interval computation for depth 15, residue 18909. -/
theorem bounds_15_18909 : exactInterval 15 18909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18909 : oddCount 18909 15 = 6 ∧ acceleratedOrbit 15 18909 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18909) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18909.1, data_15_18909.2]

/-- Complete interval computation for depth 15, residue 18910. -/
theorem bounds_15_18910 : exactInterval 15 18910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18910 : oddCount 18910 15 = 11 ∧ acceleratedOrbit 15 18910 = 102242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18910) = 3 ^ 11 * m + 102242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18910.1, data_15_18910.2]

/-- Complete interval computation for depth 15, residue 18911. -/
theorem bounds_15_18911 : exactInterval 15 18911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18911 : oddCount 18911 15 = 11 ∧ acceleratedOrbit 15 18911 = 102242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18911) = 3 ^ 11 * m + 102242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18911.1, data_15_18911.2]

/-- Complete interval computation for depth 15, residue 18912. -/
theorem bounds_15_18912 : exactInterval 15 18912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18912 : oddCount 18912 15 = 6 ∧ acceleratedOrbit 15 18912 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18912) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18912.1, data_15_18912.2]

/-- Complete interval computation for depth 15, residue 18913. -/
theorem bounds_15_18913 : exactInterval 15 18913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18913 : oddCount 18913 15 = 8 ∧ acceleratedOrbit 15 18913 = 3788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18913) = 3 ^ 8 * m + 3788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18913.1, data_15_18913.2]

/-- Complete interval computation for depth 15, residue 18914. -/
theorem bounds_15_18914 : exactInterval 15 18914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18914 : oddCount 18914 15 = 6 ∧ acceleratedOrbit 15 18914 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18914) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18914.1, data_15_18914.2]

/-- Complete interval computation for depth 15, residue 18915. -/
theorem bounds_15_18915 : exactInterval 15 18915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18915 : oddCount 18915 15 = 6 ∧ acceleratedOrbit 15 18915 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18915) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18915.1, data_15_18915.2]

/-- Complete interval computation for depth 15, residue 18916. -/
theorem bounds_15_18916 : exactInterval 15 18916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18916 : oddCount 18916 15 = 6 ∧ acceleratedOrbit 15 18916 = 421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18916) = 3 ^ 6 * m + 421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18916.1, data_15_18916.2]

/-- Complete interval computation for depth 15, residue 18917. -/
theorem bounds_15_18917 : exactInterval 15 18917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18917 : oddCount 18917 15 = 6 ∧ acceleratedOrbit 15 18917 = 421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18917) = 3 ^ 6 * m + 421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18917.1, data_15_18917.2]

/-- Complete interval computation for depth 15, residue 18918. -/
theorem bounds_15_18918 : exactInterval 15 18918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18918 : oddCount 18918 15 = 6 ∧ acceleratedOrbit 15 18918 = 421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18918) = 3 ^ 6 * m + 421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18918.1, data_15_18918.2]

/-- Complete interval computation for depth 15, residue 18919. -/
theorem bounds_15_18919 : exactInterval 15 18919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18919 : oddCount 18919 15 = 10 ∧ acceleratedOrbit 15 18919 = 34096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18919) = 3 ^ 10 * m + 34096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18919.1, data_15_18919.2]

/-- Complete interval computation for depth 15, residue 18920. -/
theorem bounds_15_18920 : exactInterval 15 18920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18920 : oddCount 18920 15 = 6 ∧ acceleratedOrbit 15 18920 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18920) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18920.1, data_15_18920.2]

/-- Complete interval computation for depth 15, residue 18921. -/
theorem bounds_15_18921 : exactInterval 15 18921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18921 : oddCount 18921 15 = 11 ∧ acceleratedOrbit 15 18921 = 102302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18921) = 3 ^ 11 * m + 102302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18921.1, data_15_18921.2]

/-- Complete interval computation for depth 15, residue 18922. -/
theorem bounds_15_18922 : exactInterval 15 18922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18922 : oddCount 18922 15 = 6 ∧ acceleratedOrbit 15 18922 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18922) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18922.1, data_15_18922.2]

/-- Complete interval computation for depth 15, residue 18923. -/
theorem bounds_15_18923 : exactInterval 15 18923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18923 : oddCount 18923 15 = 9 ∧ acceleratedOrbit 15 18923 = 11368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18923) = 3 ^ 9 * m + 11368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18923.1, data_15_18923.2]

/-- Complete interval computation for depth 15, residue 18924. -/
theorem bounds_15_18924 : exactInterval 15 18924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18924 : oddCount 18924 15 = 7 ∧ acceleratedOrbit 15 18924 = 1264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18924) = 3 ^ 7 * m + 1264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18924.1, data_15_18924.2]

/-- Complete interval computation for depth 15, residue 18925. -/
theorem bounds_15_18925 : exactInterval 15 18925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18925 : oddCount 18925 15 = 7 ∧ acceleratedOrbit 15 18925 = 1264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18925) = 3 ^ 7 * m + 1264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18925.1, data_15_18925.2]

/-- Complete interval computation for depth 15, residue 18926. -/
theorem bounds_15_18926 : exactInterval 15 18926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18926 : oddCount 18926 15 = 7 ∧ acceleratedOrbit 15 18926 = 1264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18926) = 3 ^ 7 * m + 1264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18926.1, data_15_18926.2]

/-- Complete interval computation for depth 15, residue 18927. -/
theorem bounds_15_18927 : exactInterval 15 18927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18927 : oddCount 18927 15 = 11 ∧ acceleratedOrbit 15 18927 = 102329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18927) = 3 ^ 11 * m + 102329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18927.1, data_15_18927.2]

/-- Complete interval computation for depth 15, residue 18928. -/
theorem bounds_15_18928 : exactInterval 15 18928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18928 : oddCount 18928 15 = 9 ∧ acceleratedOrbit 15 18928 = 11380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18928) = 3 ^ 9 * m + 11380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18928.1, data_15_18928.2]

/-- Complete interval computation for depth 15, residue 18929. -/
theorem bounds_15_18929 : exactInterval 15 18929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18929 : oddCount 18929 15 = 6 ∧ acceleratedOrbit 15 18929 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18929) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18929.1, data_15_18929.2]

/-- Complete interval computation for depth 15, residue 18930. -/
theorem bounds_15_18930 : exactInterval 15 18930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18930 : oddCount 18930 15 = 7 ∧ acceleratedOrbit 15 18930 = 1264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18930) = 3 ^ 7 * m + 1264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18930.1, data_15_18930.2]

/-- Complete interval computation for depth 15, residue 18931. -/
theorem bounds_15_18931 : exactInterval 15 18931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18931 : oddCount 18931 15 = 7 ∧ acceleratedOrbit 15 18931 = 1264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18931) = 3 ^ 7 * m + 1264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18931.1, data_15_18931.2]

/-- Complete interval computation for depth 15, residue 18932. -/
theorem bounds_15_18932 : exactInterval 15 18932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18932 : oddCount 18932 15 = 9 ∧ acceleratedOrbit 15 18932 = 11380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18932) = 3 ^ 9 * m + 11380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18932.1, data_15_18932.2]

/-- Complete interval computation for depth 15, residue 18933. -/
theorem bounds_15_18933 : exactInterval 15 18933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18933 : oddCount 18933 15 = 9 ∧ acceleratedOrbit 15 18933 = 11380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18933) = 3 ^ 9 * m + 11380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18933.1, data_15_18933.2]

/-- Complete interval computation for depth 15, residue 18934. -/
theorem bounds_15_18934 : exactInterval 15 18934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18934 : oddCount 18934 15 = 10 ∧ acceleratedOrbit 15 18934 = 34127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18934) = 3 ^ 10 * m + 34127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18934.1, data_15_18934.2]

/-- Complete interval computation for depth 15, residue 18935. -/
theorem bounds_15_18935 : exactInterval 15 18935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18935 : oddCount 18935 15 = 10 ∧ acceleratedOrbit 15 18935 = 34127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18935) = 3 ^ 10 * m + 34127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18935.1, data_15_18935.2]

/-- Complete interval computation for depth 15, residue 18936. -/
theorem bounds_15_18936 : exactInterval 15 18936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18936 : oddCount 18936 15 = 9 ∧ acceleratedOrbit 15 18936 = 11380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18936) = 3 ^ 9 * m + 11380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18936.1, data_15_18936.2]

/-- Complete interval computation for depth 15, residue 18937. -/
theorem bounds_15_18937 : exactInterval 15 18937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18937 : oddCount 18937 15 = 9 ∧ acceleratedOrbit 15 18937 = 11377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18937) = 3 ^ 9 * m + 11377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18937.1, data_15_18937.2]

/-- Complete interval computation for depth 15, residue 18938. -/
theorem bounds_15_18938 : exactInterval 15 18938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18938 : oddCount 18938 15 = 9 ∧ acceleratedOrbit 15 18938 = 11380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18938) = 3 ^ 9 * m + 11380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18938.1, data_15_18938.2]

end Collatz.Research.PassageAtlas.Batch0578
