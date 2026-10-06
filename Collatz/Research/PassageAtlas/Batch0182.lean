import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0182

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5931. -/
theorem bounds_15_5931 : exactInterval 15 5931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5931 : oddCount 5931 15 = 5 ∧ acceleratedOrbit 15 5931 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5931) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5931.1, data_15_5931.2]

/-- Complete interval computation for depth 15, residue 5932. -/
theorem bounds_15_5932 : exactInterval 15 5932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5932 : oddCount 5932 15 = 7 ∧ acceleratedOrbit 15 5932 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5932) = 3 ^ 7 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5932.1, data_15_5932.2]

/-- Complete interval computation for depth 15, residue 5933. -/
theorem bounds_15_5933 : exactInterval 15 5933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5933 : oddCount 5933 15 = 7 ∧ acceleratedOrbit 15 5933 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5933) = 3 ^ 7 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5933.1, data_15_5933.2]

/-- Complete interval computation for depth 15, residue 5934. -/
theorem bounds_15_5934 : exactInterval 15 5934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5934 : oddCount 5934 15 = 7 ∧ acceleratedOrbit 15 5934 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5934) = 3 ^ 7 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5934.1, data_15_5934.2]

/-- Complete interval computation for depth 15, residue 5935. -/
theorem bounds_15_5935 : exactInterval 15 5935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5935 : oddCount 5935 15 = 8 ∧ acceleratedOrbit 15 5935 = 1189 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5935) = 3 ^ 8 * m + 1189 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5935.1, data_15_5935.2]

/-- Complete interval computation for depth 15, residue 5936. -/
theorem bounds_15_5936 : exactInterval 15 5936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5936 : oddCount 5936 15 = 6 ∧ acceleratedOrbit 15 5936 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5936) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5936.1, data_15_5936.2]

/-- Complete interval computation for depth 15, residue 5937. -/
theorem bounds_15_5937 : exactInterval 15 5937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5937 : oddCount 5937 15 = 7 ∧ acceleratedOrbit 15 5937 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5937) = 3 ^ 7 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5937.1, data_15_5937.2]

/-- Complete interval computation for depth 15, residue 5938. -/
theorem bounds_15_5938 : exactInterval 15 5938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5938 : oddCount 5938 15 = 7 ∧ acceleratedOrbit 15 5938 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5938) = 3 ^ 7 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5938.1, data_15_5938.2]

/-- Complete interval computation for depth 15, residue 5939. -/
theorem bounds_15_5939 : exactInterval 15 5939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5939 : oddCount 5939 15 = 7 ∧ acceleratedOrbit 15 5939 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5939) = 3 ^ 7 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5939.1, data_15_5939.2]

/-- Complete interval computation for depth 15, residue 5940. -/
theorem bounds_15_5940 : exactInterval 15 5940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5940 : oddCount 5940 15 = 6 ∧ acceleratedOrbit 15 5940 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5940) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5940.1, data_15_5940.2]

/-- Complete interval computation for depth 15, residue 5941. -/
theorem bounds_15_5941 : exactInterval 15 5941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5941 : oddCount 5941 15 = 6 ∧ acceleratedOrbit 15 5941 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5941) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5941.1, data_15_5941.2]

/-- Complete interval computation for depth 15, residue 5942. -/
theorem bounds_15_5942 : exactInterval 15 5942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5942 : oddCount 5942 15 = 7 ∧ acceleratedOrbit 15 5942 = 397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5942) = 3 ^ 7 * m + 397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5942.1, data_15_5942.2]

/-- Complete interval computation for depth 15, residue 5943. -/
theorem bounds_15_5943 : exactInterval 15 5943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5943 : oddCount 5943 15 = 7 ∧ acceleratedOrbit 15 5943 = 397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5943) = 3 ^ 7 * m + 397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5943.1, data_15_5943.2]

/-- Complete interval computation for depth 15, residue 5944. -/
theorem bounds_15_5944 : exactInterval 15 5944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5944 : oddCount 5944 15 = 9 ∧ acceleratedOrbit 15 5944 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5944) = 3 ^ 9 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5944.1, data_15_5944.2]

/-- Complete interval computation for depth 15, residue 5945. -/
theorem bounds_15_5945 : exactInterval 15 5945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5945 : oddCount 5945 15 = 7 ∧ acceleratedOrbit 15 5945 = 397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5945) = 3 ^ 7 * m + 397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5945.1, data_15_5945.2]

/-- Complete interval computation for depth 15, residue 5946. -/
theorem bounds_15_5946 : exactInterval 15 5946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5946 : oddCount 5946 15 = 9 ∧ acceleratedOrbit 15 5946 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5946) = 3 ^ 9 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5946.1, data_15_5946.2]

/-- Complete interval computation for depth 15, residue 5947. -/
theorem bounds_15_5947 : exactInterval 15 5947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5947 : oddCount 5947 15 = 7 ∧ acceleratedOrbit 15 5947 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5947) = 3 ^ 7 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5947.1, data_15_5947.2]

/-- Complete interval computation for depth 15, residue 5948. -/
theorem bounds_15_5948 : exactInterval 15 5948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5948 : oddCount 5948 15 = 9 ∧ acceleratedOrbit 15 5948 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5948) = 3 ^ 9 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5948.1, data_15_5948.2]

/-- Complete interval computation for depth 15, residue 5949. -/
theorem bounds_15_5949 : exactInterval 15 5949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5949 : oddCount 5949 15 = 9 ∧ acceleratedOrbit 15 5949 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5949) = 3 ^ 9 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5949.1, data_15_5949.2]

/-- Complete interval computation for depth 15, residue 5950. -/
theorem bounds_15_5950 : exactInterval 15 5950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5950 : oddCount 5950 15 = 8 ∧ acceleratedOrbit 15 5950 = 1192 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5950) = 3 ^ 8 * m + 1192 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5950.1, data_15_5950.2]

/-- Complete interval computation for depth 15, residue 5951. -/
theorem bounds_15_5951 : exactInterval 15 5951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5951 : oddCount 5951 15 = 8 ∧ acceleratedOrbit 15 5951 = 1192 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5951) = 3 ^ 8 * m + 1192 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5951.1, data_15_5951.2]

/-- Complete interval computation for depth 15, residue 5952. -/
theorem bounds_15_5952 : exactInterval 15 5952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5952 : oddCount 5952 15 = 3 ∧ acceleratedOrbit 15 5952 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5952) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5952.1, data_15_5952.2]

/-- Complete interval computation for depth 15, residue 5953. -/
theorem bounds_15_5953 : exactInterval 15 5953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5953 : oddCount 5953 15 = 6 ∧ acceleratedOrbit 15 5953 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5953) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5953.1, data_15_5953.2]

/-- Complete interval computation for depth 15, residue 5954. -/
theorem bounds_15_5954 : exactInterval 15 5954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5954 : oddCount 5954 15 = 7 ∧ acceleratedOrbit 15 5954 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5954) = 3 ^ 7 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5954.1, data_15_5954.2]

/-- Complete interval computation for depth 15, residue 5955. -/
theorem bounds_15_5955 : exactInterval 15 5955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5955 : oddCount 5955 15 = 7 ∧ acceleratedOrbit 15 5955 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5955) = 3 ^ 7 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5955.1, data_15_5955.2]

/-- Complete interval computation for depth 15, residue 5956. -/
theorem bounds_15_5956 : exactInterval 15 5956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5956 : oddCount 5956 15 = 6 ∧ acceleratedOrbit 15 5956 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5956) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5956.1, data_15_5956.2]

/-- Complete interval computation for depth 15, residue 5957. -/
theorem bounds_15_5957 : exactInterval 15 5957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5957 : oddCount 5957 15 = 6 ∧ acceleratedOrbit 15 5957 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5957) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5957.1, data_15_5957.2]

/-- Complete interval computation for depth 15, residue 5958. -/
theorem bounds_15_5958 : exactInterval 15 5958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5958 : oddCount 5958 15 = 6 ∧ acceleratedOrbit 15 5958 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5958) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5958.1, data_15_5958.2]

/-- Complete interval computation for depth 15, residue 5959. -/
theorem bounds_15_5959 : exactInterval 15 5959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5959 : oddCount 5959 15 = 9 ∧ acceleratedOrbit 15 5959 = 3581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5959) = 3 ^ 9 * m + 3581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5959.1, data_15_5959.2]

/-- Complete interval computation for depth 15, residue 5960. -/
theorem bounds_15_5960 : exactInterval 15 5960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5960 : oddCount 5960 15 = 9 ∧ acceleratedOrbit 15 5960 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5960) = 3 ^ 9 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5960.1, data_15_5960.2]

/-- Complete interval computation for depth 15, residue 5961. -/
theorem bounds_15_5961 : exactInterval 15 5961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5961 : oddCount 5961 15 = 9 ∧ acceleratedOrbit 15 5961 = 3584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5961) = 3 ^ 9 * m + 3584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5961.1, data_15_5961.2]

/-- Complete interval computation for depth 15, residue 5962. -/
theorem bounds_15_5962 : exactInterval 15 5962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5962 : oddCount 5962 15 = 9 ∧ acceleratedOrbit 15 5962 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5962) = 3 ^ 9 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5962.1, data_15_5962.2]

end Collatz.Research.PassageAtlas.Batch0182
