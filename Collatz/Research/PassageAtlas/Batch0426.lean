import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0426

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13926. -/
theorem bounds_15_13926 : exactInterval 15 13926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13926 : oddCount 13926 15 = 7 ∧ acceleratedOrbit 15 13926 = 931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13926) = 3 ^ 7 * m + 931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13926.1, data_15_13926.2]

/-- Complete interval computation for depth 15, residue 13927. -/
theorem bounds_15_13927 : exactInterval 15 13927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13927 : oddCount 13927 15 = 10 ∧ acceleratedOrbit 15 13927 = 25100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13927) = 3 ^ 10 * m + 25100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13927.1, data_15_13927.2]

/-- Complete interval computation for depth 15, residue 13928. -/
theorem bounds_15_13928 : exactInterval 15 13928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13928 : oddCount 13928 15 = 4 ∧ acceleratedOrbit 15 13928 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13928) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13928.1, data_15_13928.2]

/-- Complete interval computation for depth 15, residue 13929. -/
theorem bounds_15_13929 : exactInterval 15 13929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13929 : oddCount 13929 15 = 10 ∧ acceleratedOrbit 15 13929 = 25105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13929) = 3 ^ 10 * m + 25105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13929.1, data_15_13929.2]

/-- Complete interval computation for depth 15, residue 13930. -/
theorem bounds_15_13930 : exactInterval 15 13930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13930 : oddCount 13930 15 = 4 ∧ acceleratedOrbit 15 13930 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13930) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13930.1, data_15_13930.2]

/-- Complete interval computation for depth 15, residue 13931. -/
theorem bounds_15_13931 : exactInterval 15 13931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13931 : oddCount 13931 15 = 11 ∧ acceleratedOrbit 15 13931 = 75329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13931) = 3 ^ 11 * m + 75329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13931.1, data_15_13931.2]

/-- Complete interval computation for depth 15, residue 13932. -/
theorem bounds_15_13932 : exactInterval 15 13932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13932 : oddCount 13932 15 = 8 ∧ acceleratedOrbit 15 13932 = 2791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13932) = 3 ^ 8 * m + 2791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13932.1, data_15_13932.2]

/-- Complete interval computation for depth 15, residue 13933. -/
theorem bounds_15_13933 : exactInterval 15 13933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13933 : oddCount 13933 15 = 8 ∧ acceleratedOrbit 15 13933 = 2791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13933) = 3 ^ 8 * m + 2791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13933.1, data_15_13933.2]

/-- Complete interval computation for depth 15, residue 13934. -/
theorem bounds_15_13934 : exactInterval 15 13934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13934 : oddCount 13934 15 = 8 ∧ acceleratedOrbit 15 13934 = 2791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13934) = 3 ^ 8 * m + 2791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13934.1, data_15_13934.2]

/-- Complete interval computation for depth 15, residue 13935. -/
theorem bounds_15_13935 : exactInterval 15 13935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13935 : oddCount 13935 15 = 9 ∧ acceleratedOrbit 15 13935 = 8372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13935) = 3 ^ 9 * m + 8372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13935.1, data_15_13935.2]

/-- Complete interval computation for depth 15, residue 13936. -/
theorem bounds_15_13936 : exactInterval 15 13936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13936 : oddCount 13936 15 = 9 ∧ acceleratedOrbit 15 13936 = 8383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13936) = 3 ^ 9 * m + 8383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13936.1, data_15_13936.2]

/-- Complete interval computation for depth 15, residue 13937. -/
theorem bounds_15_13937 : exactInterval 15 13937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13937 : oddCount 13937 15 = 4 ∧ acceleratedOrbit 15 13937 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13937) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13937.1, data_15_13937.2]

/-- Complete interval computation for depth 15, residue 13938. -/
theorem bounds_15_13938 : exactInterval 15 13938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13938 : oddCount 13938 15 = 8 ∧ acceleratedOrbit 15 13938 = 2792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13938) = 3 ^ 8 * m + 2792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13938.1, data_15_13938.2]

/-- Complete interval computation for depth 15, residue 13939. -/
theorem bounds_15_13939 : exactInterval 15 13939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13939 : oddCount 13939 15 = 8 ∧ acceleratedOrbit 15 13939 = 2792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13939) = 3 ^ 8 * m + 2792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13939.1, data_15_13939.2]

/-- Complete interval computation for depth 15, residue 13940. -/
theorem bounds_15_13940 : exactInterval 15 13940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13940 : oddCount 13940 15 = 9 ∧ acceleratedOrbit 15 13940 = 8383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13940) = 3 ^ 9 * m + 8383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13940.1, data_15_13940.2]

/-- Complete interval computation for depth 15, residue 13941. -/
theorem bounds_15_13941 : exactInterval 15 13941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13941 : oddCount 13941 15 = 9 ∧ acceleratedOrbit 15 13941 = 8383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13941) = 3 ^ 9 * m + 8383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13941.1, data_15_13941.2]

/-- Complete interval computation for depth 15, residue 13942. -/
theorem bounds_15_13942 : exactInterval 15 13942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13942 : oddCount 13942 15 = 8 ∧ acceleratedOrbit 15 13942 = 2794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13942) = 3 ^ 8 * m + 2794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13942.1, data_15_13942.2]

/-- Complete interval computation for depth 15, residue 13943. -/
theorem bounds_15_13943 : exactInterval 15 13943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13943 : oddCount 13943 15 = 8 ∧ acceleratedOrbit 15 13943 = 2794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13943) = 3 ^ 8 * m + 2794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13943.1, data_15_13943.2]

/-- Complete interval computation for depth 15, residue 13944. -/
theorem bounds_15_13944 : exactInterval 15 13944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13944 : oddCount 13944 15 = 9 ∧ acceleratedOrbit 15 13944 = 8383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13944) = 3 ^ 9 * m + 8383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13944.1, data_15_13944.2]

/-- Complete interval computation for depth 15, residue 13945. -/
theorem bounds_15_13945 : exactInterval 15 13945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13945 : oddCount 13945 15 = 10 ∧ acceleratedOrbit 15 13945 = 25136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13945) = 3 ^ 10 * m + 25136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13945.1, data_15_13945.2]

/-- Complete interval computation for depth 15, residue 13946. -/
theorem bounds_15_13946 : exactInterval 15 13946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13946 : oddCount 13946 15 = 9 ∧ acceleratedOrbit 15 13946 = 8383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13946) = 3 ^ 9 * m + 8383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13946.1, data_15_13946.2]

/-- Complete interval computation for depth 15, residue 13947. -/
theorem bounds_15_13947 : exactInterval 15 13947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13947 : oddCount 13947 15 = 8 ∧ acceleratedOrbit 15 13947 = 2794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13947) = 3 ^ 8 * m + 2794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13947.1, data_15_13947.2]

/-- Complete interval computation for depth 15, residue 13948. -/
theorem bounds_15_13948 : exactInterval 15 13948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13948 : oddCount 13948 15 = 9 ∧ acceleratedOrbit 15 13948 = 8381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13948) = 3 ^ 9 * m + 8381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13948.1, data_15_13948.2]

/-- Complete interval computation for depth 15, residue 13949. -/
theorem bounds_15_13949 : exactInterval 15 13949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13949 : oddCount 13949 15 = 9 ∧ acceleratedOrbit 15 13949 = 8381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13949) = 3 ^ 9 * m + 8381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13949.1, data_15_13949.2]

/-- Complete interval computation for depth 15, residue 13950. -/
theorem bounds_15_13950 : exactInterval 15 13950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13950 : oddCount 13950 15 = 9 ∧ acceleratedOrbit 15 13950 = 8381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13950) = 3 ^ 9 * m + 8381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13950.1, data_15_13950.2]

/-- Complete interval computation for depth 15, residue 13951. -/
theorem bounds_15_13951 : exactInterval 15 13951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13951 : oddCount 13951 15 = 10 ∧ acceleratedOrbit 15 13951 = 25142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13951) = 3 ^ 10 * m + 25142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13951.1, data_15_13951.2]

/-- Complete interval computation for depth 15, residue 13952. -/
theorem bounds_15_13952 : exactInterval 15 13952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13952 : oddCount 13952 15 = 5 ∧ acceleratedOrbit 15 13952 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13952) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13952.1, data_15_13952.2]

/-- Complete interval computation for depth 15, residue 13953. -/
theorem bounds_15_13953 : exactInterval 15 13953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13953 : oddCount 13953 15 = 11 ∧ acceleratedOrbit 15 13953 = 75451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13953) = 3 ^ 11 * m + 75451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13953.1, data_15_13953.2]

/-- Complete interval computation for depth 15, residue 13954. -/
theorem bounds_15_13954 : exactInterval 15 13954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13954 : oddCount 13954 15 = 4 ∧ acceleratedOrbit 15 13954 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13954) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13954.1, data_15_13954.2]

/-- Complete interval computation for depth 15, residue 13955. -/
theorem bounds_15_13955 : exactInterval 15 13955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13955 : oddCount 13955 15 = 4 ∧ acceleratedOrbit 15 13955 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13955) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13955.1, data_15_13955.2]

/-- Complete interval computation for depth 15, residue 13956. -/
theorem bounds_15_13956 : exactInterval 15 13956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13956 : oddCount 13956 15 = 8 ∧ acceleratedOrbit 15 13956 = 2798 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13956) = 3 ^ 8 * m + 2798 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13956.1, data_15_13956.2]

/-- Complete interval computation for depth 15, residue 13957. -/
theorem bounds_15_13957 : exactInterval 15 13957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13957 : oddCount 13957 15 = 8 ∧ acceleratedOrbit 15 13957 = 2798 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13957) = 3 ^ 8 * m + 2798 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13957.1, data_15_13957.2]

/-- Complete interval computation for depth 15, residue 13958. -/
theorem bounds_15_13958 : exactInterval 15 13958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13958 : oddCount 13958 15 = 8 ∧ acceleratedOrbit 15 13958 = 2798 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13958) = 3 ^ 8 * m + 2798 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13958.1, data_15_13958.2]

end Collatz.Research.PassageAtlas.Batch0426
