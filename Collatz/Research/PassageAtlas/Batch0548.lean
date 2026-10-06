import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0548

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17924. -/
theorem bounds_15_17924 : exactInterval 15 17924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17924 : oddCount 17924 15 = 5 ∧ acceleratedOrbit 15 17924 = 133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17924) = 3 ^ 5 * m + 133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17924.1, data_15_17924.2]

/-- Complete interval computation for depth 15, residue 17925. -/
theorem bounds_15_17925 : exactInterval 15 17925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17925 : oddCount 17925 15 = 5 ∧ acceleratedOrbit 15 17925 = 133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17925) = 3 ^ 5 * m + 133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17925.1, data_15_17925.2]

/-- Complete interval computation for depth 15, residue 17926. -/
theorem bounds_15_17926 : exactInterval 15 17926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17926 : oddCount 17926 15 = 5 ∧ acceleratedOrbit 15 17926 = 133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17926) = 3 ^ 5 * m + 133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17926.1, data_15_17926.2]

/-- Complete interval computation for depth 15, residue 17927. -/
theorem bounds_15_17927 : exactInterval 15 17927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17927 : oddCount 17927 15 = 9 ∧ acceleratedOrbit 15 17927 = 10772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17927) = 3 ^ 9 * m + 10772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17927.1, data_15_17927.2]

/-- Complete interval computation for depth 15, residue 17928. -/
theorem bounds_15_17928 : exactInterval 15 17928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17928 : oddCount 17928 15 = 6 ∧ acceleratedOrbit 15 17928 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17928) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17928.1, data_15_17928.2]

/-- Complete interval computation for depth 15, residue 17929. -/
theorem bounds_15_17929 : exactInterval 15 17929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17929 : oddCount 17929 15 = 10 ∧ acceleratedOrbit 15 17929 = 32318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17929) = 3 ^ 10 * m + 32318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17929.1, data_15_17929.2]

/-- Complete interval computation for depth 15, residue 17930. -/
theorem bounds_15_17930 : exactInterval 15 17930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17930 : oddCount 17930 15 = 6 ∧ acceleratedOrbit 15 17930 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17930) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17930.1, data_15_17930.2]

/-- Complete interval computation for depth 15, residue 17931. -/
theorem bounds_15_17931 : exactInterval 15 17931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17931 : oddCount 17931 15 = 5 ∧ acceleratedOrbit 15 17931 = 133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17931) = 3 ^ 5 * m + 133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17931.1, data_15_17931.2]

/-- Complete interval computation for depth 15, residue 17932. -/
theorem bounds_15_17932 : exactInterval 15 17932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17932 : oddCount 17932 15 = 6 ∧ acceleratedOrbit 15 17932 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17932) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17932.1, data_15_17932.2]

/-- Complete interval computation for depth 15, residue 17933. -/
theorem bounds_15_17933 : exactInterval 15 17933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17933 : oddCount 17933 15 = 6 ∧ acceleratedOrbit 15 17933 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17933) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17933.1, data_15_17933.2]

/-- Complete interval computation for depth 15, residue 17934. -/
theorem bounds_15_17934 : exactInterval 15 17934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17934 : oddCount 17934 15 = 8 ∧ acceleratedOrbit 15 17934 = 3592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17934) = 3 ^ 8 * m + 3592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17934.1, data_15_17934.2]

/-- Complete interval computation for depth 15, residue 17935. -/
theorem bounds_15_17935 : exactInterval 15 17935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17935 : oddCount 17935 15 = 8 ∧ acceleratedOrbit 15 17935 = 3592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17935) = 3 ^ 8 * m + 3592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17935.1, data_15_17935.2]

/-- Complete interval computation for depth 15, residue 17936. -/
theorem bounds_15_17936 : exactInterval 15 17936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17936 : oddCount 17936 15 = 6 ∧ acceleratedOrbit 15 17936 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17936) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17936.1, data_15_17936.2]

/-- Complete interval computation for depth 15, residue 17937. -/
theorem bounds_15_17937 : exactInterval 15 17937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17937 : oddCount 17937 15 = 6 ∧ acceleratedOrbit 15 17937 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17937) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17937.1, data_15_17937.2]

/-- Complete interval computation for depth 15, residue 17938. -/
theorem bounds_15_17938 : exactInterval 15 17938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17938 : oddCount 17938 15 = 8 ∧ acceleratedOrbit 15 17938 = 3593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17938) = 3 ^ 8 * m + 3593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17938.1, data_15_17938.2]

/-- Complete interval computation for depth 15, residue 17939. -/
theorem bounds_15_17939 : exactInterval 15 17939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17939 : oddCount 17939 15 = 8 ∧ acceleratedOrbit 15 17939 = 3593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17939) = 3 ^ 8 * m + 3593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17939.1, data_15_17939.2]

/-- Complete interval computation for depth 15, residue 17940. -/
theorem bounds_15_17940 : exactInterval 15 17940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17940 : oddCount 17940 15 = 6 ∧ acceleratedOrbit 15 17940 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17940) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17940.1, data_15_17940.2]

/-- Complete interval computation for depth 15, residue 17941. -/
theorem bounds_15_17941 : exactInterval 15 17941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17941 : oddCount 17941 15 = 6 ∧ acceleratedOrbit 15 17941 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17941) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17941.1, data_15_17941.2]

/-- Complete interval computation for depth 15, residue 17942. -/
theorem bounds_15_17942 : exactInterval 15 17942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17942 : oddCount 17942 15 = 7 ∧ acceleratedOrbit 15 17942 = 1198 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17942) = 3 ^ 7 * m + 1198 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17942.1, data_15_17942.2]

/-- Complete interval computation for depth 15, residue 17943. -/
theorem bounds_15_17943 : exactInterval 15 17943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17943 : oddCount 17943 15 = 7 ∧ acceleratedOrbit 15 17943 = 1198 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17943) = 3 ^ 7 * m + 1198 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17943.1, data_15_17943.2]

/-- Complete interval computation for depth 15, residue 17944. -/
theorem bounds_15_17944 : exactInterval 15 17944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17944 : oddCount 17944 15 = 6 ∧ acceleratedOrbit 15 17944 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17944) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17944.1, data_15_17944.2]

/-- Complete interval computation for depth 15, residue 17945. -/
theorem bounds_15_17945 : exactInterval 15 17945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17945 : oddCount 17945 15 = 7 ∧ acceleratedOrbit 15 17945 = 1198 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17945) = 3 ^ 7 * m + 1198 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17945.1, data_15_17945.2]

/-- Complete interval computation for depth 15, residue 17946. -/
theorem bounds_15_17946 : exactInterval 15 17946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17946 : oddCount 17946 15 = 6 ∧ acceleratedOrbit 15 17946 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17946) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17946.1, data_15_17946.2]

/-- Complete interval computation for depth 15, residue 17947. -/
theorem bounds_15_17947 : exactInterval 15 17947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17947 : oddCount 17947 15 = 10 ∧ acceleratedOrbit 15 17947 = 32345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17947) = 3 ^ 10 * m + 32345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17947.1, data_15_17947.2]

/-- Complete interval computation for depth 15, residue 17948. -/
theorem bounds_15_17948 : exactInterval 15 17948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17948 : oddCount 17948 15 = 6 ∧ acceleratedOrbit 15 17948 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17948) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17948.1, data_15_17948.2]

/-- Complete interval computation for depth 15, residue 17949. -/
theorem bounds_15_17949 : exactInterval 15 17949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17949 : oddCount 17949 15 = 6 ∧ acceleratedOrbit 15 17949 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17949) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17949.1, data_15_17949.2]

/-- Complete interval computation for depth 15, residue 17950. -/
theorem bounds_15_17950 : exactInterval 15 17950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17950 : oddCount 17950 15 = 6 ∧ acceleratedOrbit 15 17950 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17950) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17950.1, data_15_17950.2]

/-- Complete interval computation for depth 15, residue 17951. -/
theorem bounds_15_17951 : exactInterval 15 17951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17951 : oddCount 17951 15 = 9 ∧ acceleratedOrbit 15 17951 = 10784 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17951) = 3 ^ 9 * m + 10784 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17951.1, data_15_17951.2]

/-- Complete interval computation for depth 15, residue 17952. -/
theorem bounds_15_17952 : exactInterval 15 17952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17952 : oddCount 17952 15 = 6 ∧ acceleratedOrbit 15 17952 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17952) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17952.1, data_15_17952.2]

/-- Complete interval computation for depth 15, residue 17953. -/
theorem bounds_15_17953 : exactInterval 15 17953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17953 : oddCount 17953 15 = 7 ∧ acceleratedOrbit 15 17953 = 1199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17953) = 3 ^ 7 * m + 1199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17953.1, data_15_17953.2]

/-- Complete interval computation for depth 15, residue 17954. -/
theorem bounds_15_17954 : exactInterval 15 17954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17954 : oddCount 17954 15 = 6 ∧ acceleratedOrbit 15 17954 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17954) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17954.1, data_15_17954.2]

/-- Complete interval computation for depth 15, residue 17955. -/
theorem bounds_15_17955 : exactInterval 15 17955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17955 : oddCount 17955 15 = 6 ∧ acceleratedOrbit 15 17955 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17955) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17955.1, data_15_17955.2]

end Collatz.Research.PassageAtlas.Batch0548
