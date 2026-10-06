import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0304

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9928. -/
theorem bounds_15_9928 : exactInterval 15 9928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9928 : oddCount 9928 15 = 5 ∧ acceleratedOrbit 15 9928 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9928) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9928.1, data_15_9928.2]

/-- Complete interval computation for depth 15, residue 9929. -/
theorem bounds_15_9929 : exactInterval 15 9929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9929 : oddCount 9929 15 = 6 ∧ acceleratedOrbit 15 9929 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9929) = 3 ^ 6 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9929.1, data_15_9929.2]

/-- Complete interval computation for depth 15, residue 9930. -/
theorem bounds_15_9930 : exactInterval 15 9930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9930 : oddCount 9930 15 = 5 ∧ acceleratedOrbit 15 9930 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9930) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9930.1, data_15_9930.2]

/-- Complete interval computation for depth 15, residue 9931. -/
theorem bounds_15_9931 : exactInterval 15 9931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9931 : oddCount 9931 15 = 9 ∧ acceleratedOrbit 15 9931 = 5969 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9931) = 3 ^ 9 * m + 5969 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9931.1, data_15_9931.2]

/-- Complete interval computation for depth 15, residue 9932. -/
theorem bounds_15_9932 : exactInterval 15 9932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9932 : oddCount 9932 15 = 5 ∧ acceleratedOrbit 15 9932 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9932) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9932.1, data_15_9932.2]

/-- Complete interval computation for depth 15, residue 9933. -/
theorem bounds_15_9933 : exactInterval 15 9933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9933 : oddCount 9933 15 = 5 ∧ acceleratedOrbit 15 9933 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9933) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9933.1, data_15_9933.2]

/-- Complete interval computation for depth 15, residue 9934. -/
theorem bounds_15_9934 : exactInterval 15 9934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9934 : oddCount 9934 15 = 10 ∧ acceleratedOrbit 15 9934 = 17906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9934) = 3 ^ 10 * m + 17906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9934.1, data_15_9934.2]

/-- Complete interval computation for depth 15, residue 9935. -/
theorem bounds_15_9935 : exactInterval 15 9935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9935 : oddCount 9935 15 = 10 ∧ acceleratedOrbit 15 9935 = 17906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9935) = 3 ^ 10 * m + 17906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9935.1, data_15_9935.2]

/-- Complete interval computation for depth 15, residue 9936. -/
theorem bounds_15_9936 : exactInterval 15 9936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9936 : oddCount 9936 15 = 7 ∧ acceleratedOrbit 15 9936 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9936) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9936.1, data_15_9936.2]

/-- Complete interval computation for depth 15, residue 9937. -/
theorem bounds_15_9937 : exactInterval 15 9937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9937 : oddCount 9937 15 = 8 ∧ acceleratedOrbit 15 9937 = 1991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9937) = 3 ^ 8 * m + 1991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9937.1, data_15_9937.2]

/-- Complete interval computation for depth 15, residue 9938. -/
theorem bounds_15_9938 : exactInterval 15 9938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9938 : oddCount 9938 15 = 8 ∧ acceleratedOrbit 15 9938 = 1991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9938) = 3 ^ 8 * m + 1991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9938.1, data_15_9938.2]

/-- Complete interval computation for depth 15, residue 9939. -/
theorem bounds_15_9939 : exactInterval 15 9939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9939 : oddCount 9939 15 = 8 ∧ acceleratedOrbit 15 9939 = 1991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9939) = 3 ^ 8 * m + 1991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9939.1, data_15_9939.2]

/-- Complete interval computation for depth 15, residue 9940. -/
theorem bounds_15_9940 : exactInterval 15 9940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9940 : oddCount 9940 15 = 7 ∧ acceleratedOrbit 15 9940 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9940) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9940.1, data_15_9940.2]

/-- Complete interval computation for depth 15, residue 9941. -/
theorem bounds_15_9941 : exactInterval 15 9941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9941 : oddCount 9941 15 = 7 ∧ acceleratedOrbit 15 9941 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9941) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9941.1, data_15_9941.2]

/-- Complete interval computation for depth 15, residue 9942. -/
theorem bounds_15_9942 : exactInterval 15 9942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9942 : oddCount 9942 15 = 7 ∧ acceleratedOrbit 15 9942 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9942) = 3 ^ 7 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9942.1, data_15_9942.2]

/-- Complete interval computation for depth 15, residue 9943. -/
theorem bounds_15_9943 : exactInterval 15 9943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9943 : oddCount 9943 15 = 7 ∧ acceleratedOrbit 15 9943 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9943) = 3 ^ 7 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9943.1, data_15_9943.2]

/-- Complete interval computation for depth 15, residue 9944. -/
theorem bounds_15_9944 : exactInterval 15 9944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9944 : oddCount 9944 15 = 7 ∧ acceleratedOrbit 15 9944 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9944) = 3 ^ 7 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9944.1, data_15_9944.2]

/-- Complete interval computation for depth 15, residue 9945. -/
theorem bounds_15_9945 : exactInterval 15 9945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9945 : oddCount 9945 15 = 7 ∧ acceleratedOrbit 15 9945 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9945) = 3 ^ 7 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9945.1, data_15_9945.2]

/-- Complete interval computation for depth 15, residue 9946. -/
theorem bounds_15_9946 : exactInterval 15 9946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9946 : oddCount 9946 15 = 7 ∧ acceleratedOrbit 15 9946 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9946) = 3 ^ 7 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9946.1, data_15_9946.2]

/-- Complete interval computation for depth 15, residue 9947. -/
theorem bounds_15_9947 : exactInterval 15 9947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9947 : oddCount 9947 15 = 7 ∧ acceleratedOrbit 15 9947 = 664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9947) = 3 ^ 7 * m + 664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9947.1, data_15_9947.2]

/-- Complete interval computation for depth 15, residue 9948. -/
theorem bounds_15_9948 : exactInterval 15 9948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9948 : oddCount 9948 15 = 7 ∧ acceleratedOrbit 15 9948 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9948) = 3 ^ 7 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9948.1, data_15_9948.2]

/-- Complete interval computation for depth 15, residue 9949. -/
theorem bounds_15_9949 : exactInterval 15 9949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9949 : oddCount 9949 15 = 7 ∧ acceleratedOrbit 15 9949 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9949) = 3 ^ 7 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9949.1, data_15_9949.2]

/-- Complete interval computation for depth 15, residue 9950. -/
theorem bounds_15_9950 : exactInterval 15 9950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9950 : oddCount 9950 15 = 8 ∧ acceleratedOrbit 15 9950 = 1993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9950) = 3 ^ 8 * m + 1993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9950.1, data_15_9950.2]

/-- Complete interval computation for depth 15, residue 9951. -/
theorem bounds_15_9951 : exactInterval 15 9951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9951 : oddCount 9951 15 = 8 ∧ acceleratedOrbit 15 9951 = 1993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9951) = 3 ^ 8 * m + 1993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9951.1, data_15_9951.2]

/-- Complete interval computation for depth 15, residue 9952. -/
theorem bounds_15_9952 : exactInterval 15 9952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9952 : oddCount 9952 15 = 7 ∧ acceleratedOrbit 15 9952 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9952) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9952.1, data_15_9952.2]

/-- Complete interval computation for depth 15, residue 9953. -/
theorem bounds_15_9953 : exactInterval 15 9953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9953 : oddCount 9953 15 = 10 ∧ acceleratedOrbit 15 9953 = 17941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9953) = 3 ^ 10 * m + 17941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9953.1, data_15_9953.2]

/-- Complete interval computation for depth 15, residue 9954. -/
theorem bounds_15_9954 : exactInterval 15 9954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9954 : oddCount 9954 15 = 7 ∧ acceleratedOrbit 15 9954 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9954) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9954.1, data_15_9954.2]

/-- Complete interval computation for depth 15, residue 9955. -/
theorem bounds_15_9955 : exactInterval 15 9955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9955 : oddCount 9955 15 = 7 ∧ acceleratedOrbit 15 9955 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9955) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9955.1, data_15_9955.2]

/-- Complete interval computation for depth 15, residue 9956. -/
theorem bounds_15_9956 : exactInterval 15 9956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9956 : oddCount 9956 15 = 5 ∧ acceleratedOrbit 15 9956 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9956) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9956.1, data_15_9956.2]

/-- Complete interval computation for depth 15, residue 9957. -/
theorem bounds_15_9957 : exactInterval 15 9957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9957 : oddCount 9957 15 = 5 ∧ acceleratedOrbit 15 9957 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9957) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9957.1, data_15_9957.2]

/-- Complete interval computation for depth 15, residue 9958. -/
theorem bounds_15_9958 : exactInterval 15 9958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9958 : oddCount 9958 15 = 5 ∧ acceleratedOrbit 15 9958 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9958) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9958.1, data_15_9958.2]

/-- Complete interval computation for depth 15, residue 9959. -/
theorem bounds_15_9959 : exactInterval 15 9959 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9959) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9959 : oddCount 9959 15 = 9 ∧ acceleratedOrbit 15 9959 = 5983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9959) = 3 ^ 9 * m + 5983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9959.1, data_15_9959.2]

/-- Complete interval computation for depth 15, residue 9960. -/
theorem bounds_15_9960 : exactInterval 15 9960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9960 : oddCount 9960 15 = 7 ∧ acceleratedOrbit 15 9960 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9960) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9960.1, data_15_9960.2]

end Collatz.Research.PassageAtlas.Batch0304
