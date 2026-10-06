import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0762

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24936. -/
theorem bounds_15_24936 : exactInterval 15 24936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24936 : oddCount 24936 15 = 6 ∧ acceleratedOrbit 15 24936 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24936) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24936.1, data_15_24936.2]

/-- Complete interval computation for depth 15, residue 24937. -/
theorem bounds_15_24937 : exactInterval 15 24937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24937 : oddCount 24937 15 = 9 ∧ acceleratedOrbit 15 24937 = 14984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24937) = 3 ^ 9 * m + 14984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24937.1, data_15_24937.2]

/-- Complete interval computation for depth 15, residue 24938. -/
theorem bounds_15_24938 : exactInterval 15 24938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24938 : oddCount 24938 15 = 6 ∧ acceleratedOrbit 15 24938 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24938) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24938.1, data_15_24938.2]

/-- Complete interval computation for depth 15, residue 24939. -/
theorem bounds_15_24939 : exactInterval 15 24939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24939 : oddCount 24939 15 = 9 ∧ acceleratedOrbit 15 24939 = 14984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24939) = 3 ^ 9 * m + 14984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24939.1, data_15_24939.2]

/-- Complete interval computation for depth 15, residue 24940. -/
theorem bounds_15_24940 : exactInterval 15 24940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24940 : oddCount 24940 15 = 11 ∧ acceleratedOrbit 15 24940 = 134864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24940) = 3 ^ 11 * m + 134864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24940.1, data_15_24940.2]

/-- Complete interval computation for depth 15, residue 24941. -/
theorem bounds_15_24941 : exactInterval 15 24941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24941 : oddCount 24941 15 = 11 ∧ acceleratedOrbit 15 24941 = 134864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24941) = 3 ^ 11 * m + 134864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24941.1, data_15_24941.2]

/-- Complete interval computation for depth 15, residue 24942. -/
theorem bounds_15_24942 : exactInterval 15 24942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24942 : oddCount 24942 15 = 11 ∧ acceleratedOrbit 15 24942 = 134864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24942) = 3 ^ 11 * m + 134864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24942.1, data_15_24942.2]

/-- Complete interval computation for depth 15, residue 24943. -/
theorem bounds_15_24943 : exactInterval 15 24943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24943 : oddCount 24943 15 = 10 ∧ acceleratedOrbit 15 24943 = 44954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24943) = 3 ^ 10 * m + 44954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24943.1, data_15_24943.2]

/-- Complete interval computation for depth 15, residue 24944. -/
theorem bounds_15_24944 : exactInterval 15 24944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24944 : oddCount 24944 15 = 6 ∧ acceleratedOrbit 15 24944 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24944) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24944.1, data_15_24944.2]

/-- Complete interval computation for depth 15, residue 24945. -/
theorem bounds_15_24945 : exactInterval 15 24945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24945 : oddCount 24945 15 = 6 ∧ acceleratedOrbit 15 24945 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24945) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24945.1, data_15_24945.2]

/-- Complete interval computation for depth 15, residue 24946. -/
theorem bounds_15_24946 : exactInterval 15 24946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24946 : oddCount 24946 15 = 8 ∧ acceleratedOrbit 15 24946 = 4997 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24946) = 3 ^ 8 * m + 4997 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24946.1, data_15_24946.2]

/-- Complete interval computation for depth 15, residue 24947. -/
theorem bounds_15_24947 : exactInterval 15 24947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24947 : oddCount 24947 15 = 8 ∧ acceleratedOrbit 15 24947 = 4997 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24947) = 3 ^ 8 * m + 4997 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24947.1, data_15_24947.2]

/-- Complete interval computation for depth 15, residue 24948. -/
theorem bounds_15_24948 : exactInterval 15 24948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24948 : oddCount 24948 15 = 6 ∧ acceleratedOrbit 15 24948 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24948) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24948.1, data_15_24948.2]

/-- Complete interval computation for depth 15, residue 24949. -/
theorem bounds_15_24949 : exactInterval 15 24949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24949 : oddCount 24949 15 = 6 ∧ acceleratedOrbit 15 24949 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24949) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24949.1, data_15_24949.2]

/-- Complete interval computation for depth 15, residue 24950. -/
theorem bounds_15_24950 : exactInterval 15 24950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24950 : oddCount 24950 15 = 8 ∧ acceleratedOrbit 15 24950 = 4997 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24950) = 3 ^ 8 * m + 4997 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24950.1, data_15_24950.2]

/-- Complete interval computation for depth 15, residue 24951. -/
theorem bounds_15_24951 : exactInterval 15 24951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24951 : oddCount 24951 15 = 8 ∧ acceleratedOrbit 15 24951 = 4997 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24951) = 3 ^ 8 * m + 4997 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24951.1, data_15_24951.2]

/-- Complete interval computation for depth 15, residue 24952. -/
theorem bounds_15_24952 : exactInterval 15 24952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24952 : oddCount 24952 15 = 7 ∧ acceleratedOrbit 15 24952 = 1666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24952) = 3 ^ 7 * m + 1666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24952.1, data_15_24952.2]

/-- Complete interval computation for depth 15, residue 24953. -/
theorem bounds_15_24953 : exactInterval 15 24953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24953 : oddCount 24953 15 = 9 ∧ acceleratedOrbit 15 24953 = 14990 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24953) = 3 ^ 9 * m + 14990 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24953.1, data_15_24953.2]

/-- Complete interval computation for depth 15, residue 24954. -/
theorem bounds_15_24954 : exactInterval 15 24954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24954 : oddCount 24954 15 = 7 ∧ acceleratedOrbit 15 24954 = 1666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24954) = 3 ^ 7 * m + 1666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24954.1, data_15_24954.2]

/-- Complete interval computation for depth 15, residue 24955. -/
theorem bounds_15_24955 : exactInterval 15 24955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24955 : oddCount 24955 15 = 10 ∧ acceleratedOrbit 15 24955 = 44975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24955) = 3 ^ 10 * m + 44975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24955.1, data_15_24955.2]

/-- Complete interval computation for depth 15, residue 24956. -/
theorem bounds_15_24956 : exactInterval 15 24956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24956 : oddCount 24956 15 = 7 ∧ acceleratedOrbit 15 24956 = 1666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24956) = 3 ^ 7 * m + 1666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24956.1, data_15_24956.2]

/-- Complete interval computation for depth 15, residue 24957. -/
theorem bounds_15_24957 : exactInterval 15 24957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24957 : oddCount 24957 15 = 7 ∧ acceleratedOrbit 15 24957 = 1666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24957) = 3 ^ 7 * m + 1666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24957.1, data_15_24957.2]

/-- Complete interval computation for depth 15, residue 24958. -/
theorem bounds_15_24958 : exactInterval 15 24958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24958 : oddCount 24958 15 = 10 ∧ acceleratedOrbit 15 24958 = 44981 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24958) = 3 ^ 10 * m + 44981 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24958.1, data_15_24958.2]

/-- Complete interval computation for depth 15, residue 24959. -/
theorem bounds_15_24959 : exactInterval 15 24959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24959 : oddCount 24959 15 = 10 ∧ acceleratedOrbit 15 24959 = 44981 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24959) = 3 ^ 10 * m + 44981 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24959.1, data_15_24959.2]

/-- Complete interval computation for depth 15, residue 24960. -/
theorem bounds_15_24960 : exactInterval 15 24960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24960 : oddCount 24960 15 = 5 ∧ acceleratedOrbit 15 24960 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24960) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24960.1, data_15_24960.2]

/-- Complete interval computation for depth 15, residue 24961. -/
theorem bounds_15_24961 : exactInterval 15 24961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24961 : oddCount 24961 15 = 7 ∧ acceleratedOrbit 15 24961 = 1667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24961) = 3 ^ 7 * m + 1667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24961.1, data_15_24961.2]

/-- Complete interval computation for depth 15, residue 24962. -/
theorem bounds_15_24962 : exactInterval 15 24962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24962 : oddCount 24962 15 = 7 ∧ acceleratedOrbit 15 24962 = 1667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24962) = 3 ^ 7 * m + 1667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24962.1, data_15_24962.2]

/-- Complete interval computation for depth 15, residue 24963. -/
theorem bounds_15_24963 : exactInterval 15 24963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24963 : oddCount 24963 15 = 7 ∧ acceleratedOrbit 15 24963 = 1667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24963) = 3 ^ 7 * m + 1667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24963.1, data_15_24963.2]

/-- Complete interval computation for depth 15, residue 24964. -/
theorem bounds_15_24964 : exactInterval 15 24964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24964 : oddCount 24964 15 = 7 ∧ acceleratedOrbit 15 24964 = 1667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24964) = 3 ^ 7 * m + 1667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24964.1, data_15_24964.2]

/-- Complete interval computation for depth 15, residue 24965. -/
theorem bounds_15_24965 : exactInterval 15 24965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24965 : oddCount 24965 15 = 7 ∧ acceleratedOrbit 15 24965 = 1667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24965) = 3 ^ 7 * m + 1667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24965.1, data_15_24965.2]

/-- Complete interval computation for depth 15, residue 24966. -/
theorem bounds_15_24966 : exactInterval 15 24966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24966 : oddCount 24966 15 = 7 ∧ acceleratedOrbit 15 24966 = 1667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24966) = 3 ^ 7 * m + 1667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24966.1, data_15_24966.2]

/-- Complete interval computation for depth 15, residue 24967. -/
theorem bounds_15_24967 : exactInterval 15 24967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24967 : oddCount 24967 15 = 7 ∧ acceleratedOrbit 15 24967 = 1667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24967) = 3 ^ 7 * m + 1667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24967.1, data_15_24967.2]

/-- Complete interval computation for depth 15, residue 24968. -/
theorem bounds_15_24968 : exactInterval 15 24968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24968 : oddCount 24968 15 = 6 ∧ acceleratedOrbit 15 24968 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24968) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24968.1, data_15_24968.2]

end Collatz.Research.PassageAtlas.Batch0762
