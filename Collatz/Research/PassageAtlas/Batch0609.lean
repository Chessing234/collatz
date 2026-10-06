import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0609

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19922. -/
theorem bounds_15_19922 : exactInterval 15 19922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19922 : oddCount 19922 15 = 10 ∧ acceleratedOrbit 15 19922 = 35909 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19922) = 3 ^ 10 * m + 35909 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19922.1, data_15_19922.2]

/-- Complete interval computation for depth 15, residue 19923. -/
theorem bounds_15_19923 : exactInterval 15 19923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19923 : oddCount 19923 15 = 10 ∧ acceleratedOrbit 15 19923 = 35909 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19923) = 3 ^ 10 * m + 35909 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19923.1, data_15_19923.2]

/-- Complete interval computation for depth 15, residue 19924. -/
theorem bounds_15_19924 : exactInterval 15 19924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19924 : oddCount 19924 15 = 6 ∧ acceleratedOrbit 15 19924 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19924) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19924.1, data_15_19924.2]

/-- Complete interval computation for depth 15, residue 19925. -/
theorem bounds_15_19925 : exactInterval 15 19925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19925 : oddCount 19925 15 = 6 ∧ acceleratedOrbit 15 19925 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19925) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19925.1, data_15_19925.2]

/-- Complete interval computation for depth 15, residue 19926. -/
theorem bounds_15_19926 : exactInterval 15 19926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19926 : oddCount 19926 15 = 8 ∧ acceleratedOrbit 15 19926 = 3991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19926) = 3 ^ 8 * m + 3991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19926.1, data_15_19926.2]

/-- Complete interval computation for depth 15, residue 19927. -/
theorem bounds_15_19927 : exactInterval 15 19927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19927 : oddCount 19927 15 = 8 ∧ acceleratedOrbit 15 19927 = 3991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19927) = 3 ^ 8 * m + 3991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19927.1, data_15_19927.2]

/-- Complete interval computation for depth 15, residue 19928. -/
theorem bounds_15_19928 : exactInterval 15 19928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19928 : oddCount 19928 15 = 8 ∧ acceleratedOrbit 15 19928 = 3995 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19928) = 3 ^ 8 * m + 3995 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19928.1, data_15_19928.2]

/-- Complete interval computation for depth 15, residue 19929. -/
theorem bounds_15_19929 : exactInterval 15 19929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19929 : oddCount 19929 15 = 8 ∧ acceleratedOrbit 15 19929 = 3995 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19929) = 3 ^ 8 * m + 3995 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19929.1, data_15_19929.2]

/-- Complete interval computation for depth 15, residue 19930. -/
theorem bounds_15_19930 : exactInterval 15 19930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19930 : oddCount 19930 15 = 8 ∧ acceleratedOrbit 15 19930 = 3995 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19930) = 3 ^ 8 * m + 3995 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19930.1, data_15_19930.2]

/-- Complete interval computation for depth 15, residue 19931. -/
theorem bounds_15_19931 : exactInterval 15 19931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19931 : oddCount 19931 15 = 7 ∧ acceleratedOrbit 15 19931 = 1331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19931) = 3 ^ 7 * m + 1331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19931.1, data_15_19931.2]

/-- Complete interval computation for depth 15, residue 19932. -/
theorem bounds_15_19932 : exactInterval 15 19932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19932 : oddCount 19932 15 = 8 ∧ acceleratedOrbit 15 19932 = 3995 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19932) = 3 ^ 8 * m + 3995 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19932.1, data_15_19932.2]

/-- Complete interval computation for depth 15, residue 19933. -/
theorem bounds_15_19933 : exactInterval 15 19933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19933 : oddCount 19933 15 = 8 ∧ acceleratedOrbit 15 19933 = 3995 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19933) = 3 ^ 8 * m + 3995 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19933.1, data_15_19933.2]

/-- Complete interval computation for depth 15, residue 19934. -/
theorem bounds_15_19934 : exactInterval 15 19934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19934 : oddCount 19934 15 = 10 ∧ acceleratedOrbit 15 19934 = 35927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19934) = 3 ^ 10 * m + 35927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19934.1, data_15_19934.2]

/-- Complete interval computation for depth 15, residue 19935. -/
theorem bounds_15_19935 : exactInterval 15 19935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19935 : oddCount 19935 15 = 10 ∧ acceleratedOrbit 15 19935 = 35927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19935) = 3 ^ 10 * m + 35927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19935.1, data_15_19935.2]

/-- Complete interval computation for depth 15, residue 19936. -/
theorem bounds_15_19936 : exactInterval 15 19936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19936 : oddCount 19936 15 = 7 ∧ acceleratedOrbit 15 19936 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19936) = 3 ^ 7 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19936.1, data_15_19936.2]

/-- Complete interval computation for depth 15, residue 19937. -/
theorem bounds_15_19937 : exactInterval 15 19937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19937 : oddCount 19937 15 = 9 ∧ acceleratedOrbit 15 19937 = 11978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19937) = 3 ^ 9 * m + 11978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19937.1, data_15_19937.2]

/-- Complete interval computation for depth 15, residue 19938. -/
theorem bounds_15_19938 : exactInterval 15 19938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19938 : oddCount 19938 15 = 6 ∧ acceleratedOrbit 15 19938 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19938) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19938.1, data_15_19938.2]

/-- Complete interval computation for depth 15, residue 19939. -/
theorem bounds_15_19939 : exactInterval 15 19939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19939 : oddCount 19939 15 = 6 ∧ acceleratedOrbit 15 19939 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19939) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19939.1, data_15_19939.2]

/-- Complete interval computation for depth 15, residue 19940. -/
theorem bounds_15_19940 : exactInterval 15 19940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19940 : oddCount 19940 15 = 9 ∧ acceleratedOrbit 15 19940 = 11983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19940) = 3 ^ 9 * m + 11983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19940.1, data_15_19940.2]

/-- Complete interval computation for depth 15, residue 19941. -/
theorem bounds_15_19941 : exactInterval 15 19941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19941 : oddCount 19941 15 = 9 ∧ acceleratedOrbit 15 19941 = 11983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19941) = 3 ^ 9 * m + 11983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19941.1, data_15_19941.2]

/-- Complete interval computation for depth 15, residue 19942. -/
theorem bounds_15_19942 : exactInterval 15 19942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19942 : oddCount 19942 15 = 9 ∧ acceleratedOrbit 15 19942 = 11983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19942) = 3 ^ 9 * m + 11983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19942.1, data_15_19942.2]

/-- Complete interval computation for depth 15, residue 19943. -/
theorem bounds_15_19943 : exactInterval 15 19943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19943 : oddCount 19943 15 = 9 ∧ acceleratedOrbit 15 19943 = 11981 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19943) = 3 ^ 9 * m + 11981 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19943.1, data_15_19943.2]

/-- Complete interval computation for depth 15, residue 19944. -/
theorem bounds_15_19944 : exactInterval 15 19944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19944 : oddCount 19944 15 = 7 ∧ acceleratedOrbit 15 19944 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19944) = 3 ^ 7 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19944.1, data_15_19944.2]

/-- Complete interval computation for depth 15, residue 19945. -/
theorem bounds_15_19945 : exactInterval 15 19945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19945 : oddCount 19945 15 = 11 ∧ acceleratedOrbit 15 19945 = 107837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19945) = 3 ^ 11 * m + 107837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19945.1, data_15_19945.2]

/-- Complete interval computation for depth 15, residue 19946. -/
theorem bounds_15_19946 : exactInterval 15 19946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19946 : oddCount 19946 15 = 7 ∧ acceleratedOrbit 15 19946 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19946) = 3 ^ 7 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19946.1, data_15_19946.2]

/-- Complete interval computation for depth 15, residue 19947. -/
theorem bounds_15_19947 : exactInterval 15 19947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19947 : oddCount 19947 15 = 12 ∧ acceleratedOrbit 15 19947 = 323540 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19947) = 3 ^ 12 * m + 323540 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19947.1, data_15_19947.2]

/-- Complete interval computation for depth 15, residue 19948. -/
theorem bounds_15_19948 : exactInterval 15 19948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19948 : oddCount 19948 15 = 10 ∧ acceleratedOrbit 15 19948 = 35963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19948) = 3 ^ 10 * m + 35963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19948.1, data_15_19948.2]

/-- Complete interval computation for depth 15, residue 19949. -/
theorem bounds_15_19949 : exactInterval 15 19949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19949 : oddCount 19949 15 = 10 ∧ acceleratedOrbit 15 19949 = 35963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19949) = 3 ^ 10 * m + 35963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19949.1, data_15_19949.2]

/-- Complete interval computation for depth 15, residue 19950. -/
theorem bounds_15_19950 : exactInterval 15 19950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19950 : oddCount 19950 15 = 10 ∧ acceleratedOrbit 15 19950 = 35963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19950) = 3 ^ 10 * m + 35963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19950.1, data_15_19950.2]

/-- Complete interval computation for depth 15, residue 19951. -/
theorem bounds_15_19951 : exactInterval 15 19951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19951 : oddCount 19951 15 = 12 ∧ acceleratedOrbit 15 19951 = 323594 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19951) = 3 ^ 12 * m + 323594 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19951.1, data_15_19951.2]

/-- Complete interval computation for depth 15, residue 19952. -/
theorem bounds_15_19952 : exactInterval 15 19952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19952 : oddCount 19952 15 = 7 ∧ acceleratedOrbit 15 19952 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19952) = 3 ^ 7 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19952.1, data_15_19952.2]

/-- Complete interval computation for depth 15, residue 19953. -/
theorem bounds_15_19953 : exactInterval 15 19953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19953 : oddCount 19953 15 = 7 ∧ acceleratedOrbit 15 19953 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19953) = 3 ^ 7 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19953.1, data_15_19953.2]

/-- Complete interval computation for depth 15, residue 19954. -/
theorem bounds_15_19954 : exactInterval 15 19954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19954 : oddCount 19954 15 = 5 ∧ acceleratedOrbit 15 19954 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19954) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19954.1, data_15_19954.2]

end Collatz.Research.PassageAtlas.Batch0609
