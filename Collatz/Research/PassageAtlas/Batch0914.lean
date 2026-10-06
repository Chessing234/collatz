import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0914

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29917. -/
theorem bounds_15_29917 : exactInterval 15 29917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29917 : oddCount 29917 15 = 9 ∧ acceleratedOrbit 15 29917 = 17975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29917) = 3 ^ 9 * m + 17975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29917.1, data_15_29917.2]

/-- Complete interval computation for depth 15, residue 29918. -/
theorem bounds_15_29918 : exactInterval 15 29918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29918 : oddCount 29918 15 = 11 ∧ acceleratedOrbit 15 29918 = 161756 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29918) = 3 ^ 11 * m + 161756 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29918.1, data_15_29918.2]

/-- Complete interval computation for depth 15, residue 29919. -/
theorem bounds_15_29919 : exactInterval 15 29919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29919 : oddCount 29919 15 = 11 ∧ acceleratedOrbit 15 29919 = 161756 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29919) = 3 ^ 11 * m + 161756 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29919.1, data_15_29919.2]

/-- Complete interval computation for depth 15, residue 29920. -/
theorem bounds_15_29920 : exactInterval 15 29920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29920 : oddCount 29920 15 = 7 ∧ acceleratedOrbit 15 29920 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29920) = 3 ^ 7 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29920.1, data_15_29920.2]

/-- Complete interval computation for depth 15, residue 29921. -/
theorem bounds_15_29921 : exactInterval 15 29921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29921 : oddCount 29921 15 = 11 ∧ acceleratedOrbit 15 29921 = 161770 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29921) = 3 ^ 11 * m + 161770 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29921.1, data_15_29921.2]

/-- Complete interval computation for depth 15, residue 29922. -/
theorem bounds_15_29922 : exactInterval 15 29922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29922 : oddCount 29922 15 = 6 ∧ acceleratedOrbit 15 29922 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29922) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29922.1, data_15_29922.2]

/-- Complete interval computation for depth 15, residue 29923. -/
theorem bounds_15_29923 : exactInterval 15 29923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29923 : oddCount 29923 15 = 6 ∧ acceleratedOrbit 15 29923 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29923) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29923.1, data_15_29923.2]

/-- Complete interval computation for depth 15, residue 29924. -/
theorem bounds_15_29924 : exactInterval 15 29924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29924 : oddCount 29924 15 = 10 ∧ acceleratedOrbit 15 29924 = 53945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29924) = 3 ^ 10 * m + 53945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29924.1, data_15_29924.2]

/-- Complete interval computation for depth 15, residue 29925. -/
theorem bounds_15_29925 : exactInterval 15 29925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29925 : oddCount 29925 15 = 10 ∧ acceleratedOrbit 15 29925 = 53945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29925) = 3 ^ 10 * m + 53945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29925.1, data_15_29925.2]

/-- Complete interval computation for depth 15, residue 29926. -/
theorem bounds_15_29926 : exactInterval 15 29926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29926 : oddCount 29926 15 = 10 ∧ acceleratedOrbit 15 29926 = 53945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29926) = 3 ^ 10 * m + 53945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29926.1, data_15_29926.2]

/-- Complete interval computation for depth 15, residue 29927. -/
theorem bounds_15_29927 : exactInterval 15 29927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29927 : oddCount 29927 15 = 11 ∧ acceleratedOrbit 15 29927 = 161797 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29927) = 3 ^ 11 * m + 161797 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29927.1, data_15_29927.2]

/-- Complete interval computation for depth 15, residue 29928. -/
theorem bounds_15_29928 : exactInterval 15 29928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29928 : oddCount 29928 15 = 7 ∧ acceleratedOrbit 15 29928 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29928) = 3 ^ 7 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29928.1, data_15_29928.2]

/-- Complete interval computation for depth 15, residue 29929. -/
theorem bounds_15_29929 : exactInterval 15 29929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29929 : oddCount 29929 15 = 9 ∧ acceleratedOrbit 15 29929 = 17981 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29929) = 3 ^ 9 * m + 17981 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29929.1, data_15_29929.2]

/-- Complete interval computation for depth 15, residue 29930. -/
theorem bounds_15_29930 : exactInterval 15 29930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29930 : oddCount 29930 15 = 7 ∧ acceleratedOrbit 15 29930 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29930) = 3 ^ 7 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29930.1, data_15_29930.2]

/-- Complete interval computation for depth 15, residue 29931. -/
theorem bounds_15_29931 : exactInterval 15 29931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29931 : oddCount 29931 15 = 10 ∧ acceleratedOrbit 15 29931 = 53941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29931) = 3 ^ 10 * m + 53941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29931.1, data_15_29931.2]

/-- Complete interval computation for depth 15, residue 29932. -/
theorem bounds_15_29932 : exactInterval 15 29932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29932 : oddCount 29932 15 = 4 ∧ acceleratedOrbit 15 29932 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29932) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29932.1, data_15_29932.2]

/-- Complete interval computation for depth 15, residue 29933. -/
theorem bounds_15_29933 : exactInterval 15 29933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29933 : oddCount 29933 15 = 4 ∧ acceleratedOrbit 15 29933 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29933) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29933.1, data_15_29933.2]

/-- Complete interval computation for depth 15, residue 29934. -/
theorem bounds_15_29934 : exactInterval 15 29934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29934 : oddCount 29934 15 = 4 ∧ acceleratedOrbit 15 29934 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29934) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29934.1, data_15_29934.2]

/-- Complete interval computation for depth 15, residue 29935. -/
theorem bounds_15_29935 : exactInterval 15 29935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29935 : oddCount 29935 15 = 14 ∧ acceleratedOrbit 15 29935 = 4369625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29935) = 3 ^ 14 * m + 4369625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29935.1, data_15_29935.2]

/-- Complete interval computation for depth 15, residue 29936. -/
theorem bounds_15_29936 : exactInterval 15 29936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29936 : oddCount 29936 15 = 7 ∧ acceleratedOrbit 15 29936 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29936) = 3 ^ 7 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29936.1, data_15_29936.2]

/-- Complete interval computation for depth 15, residue 29937. -/
theorem bounds_15_29937 : exactInterval 15 29937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29937 : oddCount 29937 15 = 7 ∧ acceleratedOrbit 15 29937 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29937) = 3 ^ 7 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29937.1, data_15_29937.2]

/-- Complete interval computation for depth 15, residue 29938. -/
theorem bounds_15_29938 : exactInterval 15 29938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29938 : oddCount 29938 15 = 8 ∧ acceleratedOrbit 15 29938 = 5996 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29938) = 3 ^ 8 * m + 5996 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29938.1, data_15_29938.2]

/-- Complete interval computation for depth 15, residue 29939. -/
theorem bounds_15_29939 : exactInterval 15 29939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29939 : oddCount 29939 15 = 8 ∧ acceleratedOrbit 15 29939 = 5996 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29939) = 3 ^ 8 * m + 5996 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29939.1, data_15_29939.2]

/-- Complete interval computation for depth 15, residue 29940. -/
theorem bounds_15_29940 : exactInterval 15 29940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29940 : oddCount 29940 15 = 7 ∧ acceleratedOrbit 15 29940 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29940) = 3 ^ 7 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29940.1, data_15_29940.2]

/-- Complete interval computation for depth 15, residue 29941. -/
theorem bounds_15_29941 : exactInterval 15 29941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29941 : oddCount 29941 15 = 7 ∧ acceleratedOrbit 15 29941 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29941) = 3 ^ 7 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29941.1, data_15_29941.2]

/-- Complete interval computation for depth 15, residue 29942. -/
theorem bounds_15_29942 : exactInterval 15 29942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29942 : oddCount 29942 15 = 7 ∧ acceleratedOrbit 15 29942 = 1999 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29942) = 3 ^ 7 * m + 1999 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29942.1, data_15_29942.2]

/-- Complete interval computation for depth 15, residue 29943. -/
theorem bounds_15_29943 : exactInterval 15 29943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29943 : oddCount 29943 15 = 7 ∧ acceleratedOrbit 15 29943 = 1999 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29943) = 3 ^ 7 * m + 1999 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29943.1, data_15_29943.2]

/-- Complete interval computation for depth 15, residue 29944. -/
theorem bounds_15_29944 : exactInterval 15 29944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29944 : oddCount 29944 15 = 9 ∧ acceleratedOrbit 15 29944 = 17992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29944) = 3 ^ 9 * m + 17992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29944.1, data_15_29944.2]

/-- Complete interval computation for depth 15, residue 29945. -/
theorem bounds_15_29945 : exactInterval 15 29945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29945 : oddCount 29945 15 = 7 ∧ acceleratedOrbit 15 29945 = 1999 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29945) = 3 ^ 7 * m + 1999 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29945.1, data_15_29945.2]

/-- Complete interval computation for depth 15, residue 29946. -/
theorem bounds_15_29946 : exactInterval 15 29946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29946 : oddCount 29946 15 = 9 ∧ acceleratedOrbit 15 29946 = 17992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29946) = 3 ^ 9 * m + 17992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29946.1, data_15_29946.2]

/-- Complete interval computation for depth 15, residue 29947. -/
theorem bounds_15_29947 : exactInterval 15 29947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29947 : oddCount 29947 15 = 9 ∧ acceleratedOrbit 15 29947 = 17990 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29947) = 3 ^ 9 * m + 17990 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29947.1, data_15_29947.2]

/-- Complete interval computation for depth 15, residue 29948. -/
theorem bounds_15_29948 : exactInterval 15 29948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29948 : oddCount 29948 15 = 9 ∧ acceleratedOrbit 15 29948 = 17992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29948) = 3 ^ 9 * m + 17992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29948.1, data_15_29948.2]

end Collatz.Research.PassageAtlas.Batch0914
