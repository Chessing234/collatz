import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0151

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4915. -/
theorem bounds_15_4915 : exactInterval 15 4915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4915 : oddCount 4915 15 = 6 ∧ acceleratedOrbit 15 4915 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4915) = 3 ^ 6 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4915.1, data_15_4915.2]

/-- Complete interval computation for depth 15, residue 4916. -/
theorem bounds_15_4916 : exactInterval 15 4916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4916 : oddCount 4916 15 = 5 ∧ acceleratedOrbit 15 4916 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4916) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4916.1, data_15_4916.2]

/-- Complete interval computation for depth 15, residue 4917. -/
theorem bounds_15_4917 : exactInterval 15 4917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4917 : oddCount 4917 15 = 5 ∧ acceleratedOrbit 15 4917 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4917) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4917.1, data_15_4917.2]

/-- Complete interval computation for depth 15, residue 4918. -/
theorem bounds_15_4918 : exactInterval 15 4918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4918 : oddCount 4918 15 = 10 ∧ acceleratedOrbit 15 4918 = 8869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4918) = 3 ^ 10 * m + 8869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4918.1, data_15_4918.2]

/-- Complete interval computation for depth 15, residue 4919. -/
theorem bounds_15_4919 : exactInterval 15 4919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4919 : oddCount 4919 15 = 10 ∧ acceleratedOrbit 15 4919 = 8869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4919) = 3 ^ 10 * m + 8869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4919.1, data_15_4919.2]

/-- Complete interval computation for depth 15, residue 4920. -/
theorem bounds_15_4920 : exactInterval 15 4920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4920 : oddCount 4920 15 = 7 ∧ acceleratedOrbit 15 4920 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4920) = 3 ^ 7 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4920.1, data_15_4920.2]

/-- Complete interval computation for depth 15, residue 4921. -/
theorem bounds_15_4921 : exactInterval 15 4921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4921 : oddCount 4921 15 = 8 ∧ acceleratedOrbit 15 4921 = 986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4921) = 3 ^ 8 * m + 986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4921.1, data_15_4921.2]

/-- Complete interval computation for depth 15, residue 4922. -/
theorem bounds_15_4922 : exactInterval 15 4922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4922 : oddCount 4922 15 = 7 ∧ acceleratedOrbit 15 4922 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4922) = 3 ^ 7 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4922.1, data_15_4922.2]

/-- Complete interval computation for depth 15, residue 4923. -/
theorem bounds_15_4923 : exactInterval 15 4923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4923 : oddCount 4923 15 = 7 ∧ acceleratedOrbit 15 4923 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4923) = 3 ^ 7 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4923.1, data_15_4923.2]

/-- Complete interval computation for depth 15, residue 4924. -/
theorem bounds_15_4924 : exactInterval 15 4924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4924 : oddCount 4924 15 = 7 ∧ acceleratedOrbit 15 4924 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4924) = 3 ^ 7 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4924.1, data_15_4924.2]

/-- Complete interval computation for depth 15, residue 4925. -/
theorem bounds_15_4925 : exactInterval 15 4925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4925 : oddCount 4925 15 = 7 ∧ acceleratedOrbit 15 4925 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4925) = 3 ^ 7 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4925.1, data_15_4925.2]

/-- Complete interval computation for depth 15, residue 4926. -/
theorem bounds_15_4926 : exactInterval 15 4926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4926 : oddCount 4926 15 = 10 ∧ acceleratedOrbit 15 4926 = 8882 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4926) = 3 ^ 10 * m + 8882 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4926.1, data_15_4926.2]

/-- Complete interval computation for depth 15, residue 4927. -/
theorem bounds_15_4927 : exactInterval 15 4927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4927 : oddCount 4927 15 = 10 ∧ acceleratedOrbit 15 4927 = 8882 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4927) = 3 ^ 10 * m + 8882 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4927.1, data_15_4927.2]

/-- Complete interval computation for depth 15, residue 4928. -/
theorem bounds_15_4928 : exactInterval 15 4928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4928 : oddCount 4928 15 = 4 ∧ acceleratedOrbit 15 4928 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4928) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4928.1, data_15_4928.2]

/-- Complete interval computation for depth 15, residue 4929. -/
theorem bounds_15_4929 : exactInterval 15 4929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4929 : oddCount 4929 15 = 5 ∧ acceleratedOrbit 15 4929 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4929) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4929.1, data_15_4929.2]

/-- Complete interval computation for depth 15, residue 4930. -/
theorem bounds_15_4930 : exactInterval 15 4930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4930 : oddCount 4930 15 = 8 ∧ acceleratedOrbit 15 4930 = 989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4930) = 3 ^ 8 * m + 989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4930.1, data_15_4930.2]

/-- Complete interval computation for depth 15, residue 4931. -/
theorem bounds_15_4931 : exactInterval 15 4931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4931 : oddCount 4931 15 = 8 ∧ acceleratedOrbit 15 4931 = 989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4931) = 3 ^ 8 * m + 989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4931.1, data_15_4931.2]

/-- Complete interval computation for depth 15, residue 4932. -/
theorem bounds_15_4932 : exactInterval 15 4932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4932 : oddCount 4932 15 = 8 ∧ acceleratedOrbit 15 4932 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4932) = 3 ^ 8 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4932.1, data_15_4932.2]

/-- Complete interval computation for depth 15, residue 4933. -/
theorem bounds_15_4933 : exactInterval 15 4933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4933 : oddCount 4933 15 = 8 ∧ acceleratedOrbit 15 4933 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4933) = 3 ^ 8 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4933.1, data_15_4933.2]

/-- Complete interval computation for depth 15, residue 4934. -/
theorem bounds_15_4934 : exactInterval 15 4934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4934 : oddCount 4934 15 = 8 ∧ acceleratedOrbit 15 4934 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4934) = 3 ^ 8 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4934.1, data_15_4934.2]

/-- Complete interval computation for depth 15, residue 4935. -/
theorem bounds_15_4935 : exactInterval 15 4935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4935 : oddCount 4935 15 = 11 ∧ acceleratedOrbit 15 4935 = 26689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4935) = 3 ^ 11 * m + 26689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4935.1, data_15_4935.2]

/-- Complete interval computation for depth 15, residue 4936. -/
theorem bounds_15_4936 : exactInterval 15 4936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4936 : oddCount 4936 15 = 8 ∧ acceleratedOrbit 15 4936 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4936) = 3 ^ 8 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4936.1, data_15_4936.2]

/-- Complete interval computation for depth 15, residue 4937. -/
theorem bounds_15_4937 : exactInterval 15 4937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4937 : oddCount 4937 15 = 6 ∧ acceleratedOrbit 15 4937 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4937) = 3 ^ 6 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4937.1, data_15_4937.2]

/-- Complete interval computation for depth 15, residue 4938. -/
theorem bounds_15_4938 : exactInterval 15 4938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4938 : oddCount 4938 15 = 8 ∧ acceleratedOrbit 15 4938 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4938) = 3 ^ 8 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4938.1, data_15_4938.2]

/-- Complete interval computation for depth 15, residue 4939. -/
theorem bounds_15_4939 : exactInterval 15 4939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4939 : oddCount 4939 15 = 8 ∧ acceleratedOrbit 15 4939 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4939) = 3 ^ 8 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4939.1, data_15_4939.2]

/-- Complete interval computation for depth 15, residue 4940. -/
theorem bounds_15_4940 : exactInterval 15 4940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4940 : oddCount 4940 15 = 8 ∧ acceleratedOrbit 15 4940 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4940) = 3 ^ 8 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4940.1, data_15_4940.2]

/-- Complete interval computation for depth 15, residue 4941. -/
theorem bounds_15_4941 : exactInterval 15 4941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4941 : oddCount 4941 15 = 8 ∧ acceleratedOrbit 15 4941 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4941) = 3 ^ 8 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4941.1, data_15_4941.2]

/-- Complete interval computation for depth 15, residue 4942. -/
theorem bounds_15_4942 : exactInterval 15 4942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4942 : oddCount 4942 15 = 6 ∧ acceleratedOrbit 15 4942 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4942) = 3 ^ 6 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4942.1, data_15_4942.2]

/-- Complete interval computation for depth 15, residue 4943. -/
theorem bounds_15_4943 : exactInterval 15 4943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4943 : oddCount 4943 15 = 6 ∧ acceleratedOrbit 15 4943 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4943) = 3 ^ 6 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4943.1, data_15_4943.2]

/-- Complete interval computation for depth 15, residue 4944. -/
theorem bounds_15_4944 : exactInterval 15 4944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4944 : oddCount 4944 15 = 4 ∧ acceleratedOrbit 15 4944 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4944) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4944.1, data_15_4944.2]

/-- Complete interval computation for depth 15, residue 4945. -/
theorem bounds_15_4945 : exactInterval 15 4945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4945 : oddCount 4945 15 = 8 ∧ acceleratedOrbit 15 4945 = 991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4945) = 3 ^ 8 * m + 991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4945.1, data_15_4945.2]

/-- Complete interval computation for depth 15, residue 4946. -/
theorem bounds_15_4946 : exactInterval 15 4946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4946 : oddCount 4946 15 = 8 ∧ acceleratedOrbit 15 4946 = 991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4946) = 3 ^ 8 * m + 991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4946.1, data_15_4946.2]

end Collatz.Research.PassageAtlas.Batch0151
