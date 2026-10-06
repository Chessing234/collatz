import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0243

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7929. -/
theorem bounds_15_7929 : exactInterval 15 7929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7929 : oddCount 7929 15 = 7 ∧ acceleratedOrbit 15 7929 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7929) = 3 ^ 7 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7929.1, data_15_7929.2]

/-- Complete interval computation for depth 15, residue 7930. -/
theorem bounds_15_7930 : exactInterval 15 7930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7930 : oddCount 7930 15 = 9 ∧ acceleratedOrbit 15 7930 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7930) = 3 ^ 9 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7930.1, data_15_7930.2]

/-- Complete interval computation for depth 15, residue 7931. -/
theorem bounds_15_7931 : exactInterval 15 7931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7931 : oddCount 7931 15 = 10 ∧ acceleratedOrbit 15 7931 = 14296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7931) = 3 ^ 10 * m + 14296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7931.1, data_15_7931.2]

/-- Complete interval computation for depth 15, residue 7932. -/
theorem bounds_15_7932 : exactInterval 15 7932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7932 : oddCount 7932 15 = 8 ∧ acceleratedOrbit 15 7932 = 1589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7932) = 3 ^ 8 * m + 1589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7932.1, data_15_7932.2]

/-- Complete interval computation for depth 15, residue 7933. -/
theorem bounds_15_7933 : exactInterval 15 7933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7933 : oddCount 7933 15 = 8 ∧ acceleratedOrbit 15 7933 = 1589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7933) = 3 ^ 8 * m + 1589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7933.1, data_15_7933.2]

/-- Complete interval computation for depth 15, residue 7934. -/
theorem bounds_15_7934 : exactInterval 15 7934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7934 : oddCount 7934 15 = 8 ∧ acceleratedOrbit 15 7934 = 1589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7934) = 3 ^ 8 * m + 1589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7934.1, data_15_7934.2]

/-- Complete interval computation for depth 15, residue 7935. -/
theorem bounds_15_7935 : exactInterval 15 7935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7935 : oddCount 7935 15 = 14 ∧ acceleratedOrbit 15 7935 = 1158380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7935) = 3 ^ 14 * m + 1158380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7935.1, data_15_7935.2]

/-- Complete interval computation for depth 15, residue 7936. -/
theorem bounds_15_7936 : exactInterval 15 7936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7936 : oddCount 7936 15 = 6 ∧ acceleratedOrbit 15 7936 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7936) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7936.1, data_15_7936.2]

/-- Complete interval computation for depth 15, residue 7937. -/
theorem bounds_15_7937 : exactInterval 15 7937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7937 : oddCount 7937 15 = 5 ∧ acceleratedOrbit 15 7937 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7937) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7937.1, data_15_7937.2]

/-- Complete interval computation for depth 15, residue 7938. -/
theorem bounds_15_7938 : exactInterval 15 7938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7938 : oddCount 7938 15 = 8 ∧ acceleratedOrbit 15 7938 = 1592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7938) = 3 ^ 8 * m + 1592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7938.1, data_15_7938.2]

/-- Complete interval computation for depth 15, residue 7939. -/
theorem bounds_15_7939 : exactInterval 15 7939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7939 : oddCount 7939 15 = 8 ∧ acceleratedOrbit 15 7939 = 1592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7939) = 3 ^ 8 * m + 1592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7939.1, data_15_7939.2]

/-- Complete interval computation for depth 15, residue 7940. -/
theorem bounds_15_7940 : exactInterval 15 7940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7940 : oddCount 7940 15 = 5 ∧ acceleratedOrbit 15 7940 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7940) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7940.1, data_15_7940.2]

/-- Complete interval computation for depth 15, residue 7941. -/
theorem bounds_15_7941 : exactInterval 15 7941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7941 : oddCount 7941 15 = 5 ∧ acceleratedOrbit 15 7941 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7941) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7941.1, data_15_7941.2]

/-- Complete interval computation for depth 15, residue 7942. -/
theorem bounds_15_7942 : exactInterval 15 7942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7942 : oddCount 7942 15 = 5 ∧ acceleratedOrbit 15 7942 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7942) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7942.1, data_15_7942.2]

/-- Complete interval computation for depth 15, residue 7943. -/
theorem bounds_15_7943 : exactInterval 15 7943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7943 : oddCount 7943 15 = 8 ∧ acceleratedOrbit 15 7943 = 1592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7943) = 3 ^ 8 * m + 1592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7943.1, data_15_7943.2]

/-- Complete interval computation for depth 15, residue 7944. -/
theorem bounds_15_7944 : exactInterval 15 7944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7944 : oddCount 7944 15 = 8 ∧ acceleratedOrbit 15 7944 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7944) = 3 ^ 8 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7944.1, data_15_7944.2]

/-- Complete interval computation for depth 15, residue 7945. -/
theorem bounds_15_7945 : exactInterval 15 7945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7945 : oddCount 7945 15 = 9 ∧ acceleratedOrbit 15 7945 = 4774 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7945) = 3 ^ 9 * m + 4774 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7945.1, data_15_7945.2]

/-- Complete interval computation for depth 15, residue 7946. -/
theorem bounds_15_7946 : exactInterval 15 7946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7946 : oddCount 7946 15 = 8 ∧ acceleratedOrbit 15 7946 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7946) = 3 ^ 8 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7946.1, data_15_7946.2]

/-- Complete interval computation for depth 15, residue 7947. -/
theorem bounds_15_7947 : exactInterval 15 7947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7947 : oddCount 7947 15 = 9 ∧ acceleratedOrbit 15 7947 = 4778 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7947) = 3 ^ 9 * m + 4778 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7947.1, data_15_7947.2]

/-- Complete interval computation for depth 15, residue 7948. -/
theorem bounds_15_7948 : exactInterval 15 7948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7948 : oddCount 7948 15 = 8 ∧ acceleratedOrbit 15 7948 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7948) = 3 ^ 8 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7948.1, data_15_7948.2]

/-- Complete interval computation for depth 15, residue 7949. -/
theorem bounds_15_7949 : exactInterval 15 7949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7949 : oddCount 7949 15 = 8 ∧ acceleratedOrbit 15 7949 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7949) = 3 ^ 8 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7949.1, data_15_7949.2]

/-- Complete interval computation for depth 15, residue 7950. -/
theorem bounds_15_7950 : exactInterval 15 7950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7950 : oddCount 7950 15 = 5 ∧ acceleratedOrbit 15 7950 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7950) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7950.1, data_15_7950.2]

/-- Complete interval computation for depth 15, residue 7951. -/
theorem bounds_15_7951 : exactInterval 15 7951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7951 : oddCount 7951 15 = 5 ∧ acceleratedOrbit 15 7951 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7951) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7951.1, data_15_7951.2]

/-- Complete interval computation for depth 15, residue 7952. -/
theorem bounds_15_7952 : exactInterval 15 7952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7952 : oddCount 7952 15 = 4 ∧ acceleratedOrbit 15 7952 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7952) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7952.1, data_15_7952.2]

/-- Complete interval computation for depth 15, residue 7953. -/
theorem bounds_15_7953 : exactInterval 15 7953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7953 : oddCount 7953 15 = 8 ∧ acceleratedOrbit 15 7953 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7953) = 3 ^ 8 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7953.1, data_15_7953.2]

/-- Complete interval computation for depth 15, residue 7954. -/
theorem bounds_15_7954 : exactInterval 15 7954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7954 : oddCount 7954 15 = 9 ∧ acceleratedOrbit 15 7954 = 4781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7954) = 3 ^ 9 * m + 4781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7954.1, data_15_7954.2]

/-- Complete interval computation for depth 15, residue 7955. -/
theorem bounds_15_7955 : exactInterval 15 7955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7955 : oddCount 7955 15 = 9 ∧ acceleratedOrbit 15 7955 = 4781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7955) = 3 ^ 9 * m + 4781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7955.1, data_15_7955.2]

/-- Complete interval computation for depth 15, residue 7956. -/
theorem bounds_15_7956 : exactInterval 15 7956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7956 : oddCount 7956 15 = 4 ∧ acceleratedOrbit 15 7956 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7956) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7956.1, data_15_7956.2]

/-- Complete interval computation for depth 15, residue 7957. -/
theorem bounds_15_7957 : exactInterval 15 7957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7957 : oddCount 7957 15 = 4 ∧ acceleratedOrbit 15 7957 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7957) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7957.1, data_15_7957.2]

/-- Complete interval computation for depth 15, residue 7958. -/
theorem bounds_15_7958 : exactInterval 15 7958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7958 : oddCount 7958 15 = 8 ∧ acceleratedOrbit 15 7958 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7958) = 3 ^ 8 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7958.1, data_15_7958.2]

/-- Complete interval computation for depth 15, residue 7959. -/
theorem bounds_15_7959 : exactInterval 15 7959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7959 : oddCount 7959 15 = 8 ∧ acceleratedOrbit 15 7959 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7959) = 3 ^ 8 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7959.1, data_15_7959.2]

/-- Complete interval computation for depth 15, residue 7960. -/
theorem bounds_15_7960 : exactInterval 15 7960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7960 : oddCount 7960 15 = 4 ∧ acceleratedOrbit 15 7960 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7960) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7960.1, data_15_7960.2]

/-- Complete interval computation for depth 15, residue 7961. -/
theorem bounds_15_7961 : exactInterval 15 7961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7961 : oddCount 7961 15 = 9 ∧ acceleratedOrbit 15 7961 = 4784 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7961) = 3 ^ 9 * m + 4784 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7961.1, data_15_7961.2]

end Collatz.Research.PassageAtlas.Batch0243
