import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0701

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22937. -/
theorem bounds_15_22937 : exactInterval 15 22937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22937 : oddCount 22937 15 = 7 ∧ acceleratedOrbit 15 22937 = 1532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22937) = 3 ^ 7 * m + 1532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22937.1, data_15_22937.2]

/-- Complete interval computation for depth 15, residue 22938. -/
theorem bounds_15_22938 : exactInterval 15 22938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22938 : oddCount 22938 15 = 6 ∧ acceleratedOrbit 15 22938 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22938) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22938.1, data_15_22938.2]

/-- Complete interval computation for depth 15, residue 22939. -/
theorem bounds_15_22939 : exactInterval 15 22939 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22939) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22939 : oddCount 22939 15 = 9 ∧ acceleratedOrbit 15 22939 = 13780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22939) = 3 ^ 9 * m + 13780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22939.1, data_15_22939.2]

/-- Complete interval computation for depth 15, residue 22940. -/
theorem bounds_15_22940 : exactInterval 15 22940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22940 : oddCount 22940 15 = 9 ∧ acceleratedOrbit 15 22940 = 13783 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22940) = 3 ^ 9 * m + 13783 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22940.1, data_15_22940.2]

/-- Complete interval computation for depth 15, residue 22941. -/
theorem bounds_15_22941 : exactInterval 15 22941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22941 : oddCount 22941 15 = 9 ∧ acceleratedOrbit 15 22941 = 13783 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22941) = 3 ^ 9 * m + 13783 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22941.1, data_15_22941.2]

/-- Complete interval computation for depth 15, residue 22942. -/
theorem bounds_15_22942 : exactInterval 15 22942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22942 : oddCount 22942 15 = 9 ∧ acceleratedOrbit 15 22942 = 13783 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22942) = 3 ^ 9 * m + 13783 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22942.1, data_15_22942.2]

/-- Complete interval computation for depth 15, residue 22943. -/
theorem bounds_15_22943 : exactInterval 15 22943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22943 : oddCount 22943 15 = 8 ∧ acceleratedOrbit 15 22943 = 4594 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22943) = 3 ^ 8 * m + 4594 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22943.1, data_15_22943.2]

/-- Complete interval computation for depth 15, residue 22944. -/
theorem bounds_15_22944 : exactInterval 15 22944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22944 : oddCount 22944 15 = 3 ∧ acceleratedOrbit 15 22944 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22944) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22944.1, data_15_22944.2]

/-- Complete interval computation for depth 15, residue 22945. -/
theorem bounds_15_22945 : exactInterval 15 22945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22945 : oddCount 22945 15 = 8 ∧ acceleratedOrbit 15 22945 = 4595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22945) = 3 ^ 8 * m + 4595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22945.1, data_15_22945.2]

/-- Complete interval computation for depth 15, residue 22946. -/
theorem bounds_15_22946 : exactInterval 15 22946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22946 : oddCount 22946 15 = 9 ∧ acceleratedOrbit 15 22946 = 13790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22946) = 3 ^ 9 * m + 13790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22946.1, data_15_22946.2]

/-- Complete interval computation for depth 15, residue 22947. -/
theorem bounds_15_22947 : exactInterval 15 22947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22947 : oddCount 22947 15 = 9 ∧ acceleratedOrbit 15 22947 = 13790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22947) = 3 ^ 9 * m + 13790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22947.1, data_15_22947.2]

/-- Complete interval computation for depth 15, residue 22948. -/
theorem bounds_15_22948 : exactInterval 15 22948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22948 : oddCount 22948 15 = 9 ∧ acceleratedOrbit 15 22948 = 13790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22948) = 3 ^ 9 * m + 13790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22948.1, data_15_22948.2]

/-- Complete interval computation for depth 15, residue 22949. -/
theorem bounds_15_22949 : exactInterval 15 22949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22949 : oddCount 22949 15 = 9 ∧ acceleratedOrbit 15 22949 = 13790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22949) = 3 ^ 9 * m + 13790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22949.1, data_15_22949.2]

/-- Complete interval computation for depth 15, residue 22950. -/
theorem bounds_15_22950 : exactInterval 15 22950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22950 : oddCount 22950 15 = 9 ∧ acceleratedOrbit 15 22950 = 13790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22950) = 3 ^ 9 * m + 13790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22950.1, data_15_22950.2]

/-- Complete interval computation for depth 15, residue 22951. -/
theorem bounds_15_22951 : exactInterval 15 22951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22951 : oddCount 22951 15 = 7 ∧ acceleratedOrbit 15 22951 = 1532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22951) = 3 ^ 7 * m + 1532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22951.1, data_15_22951.2]

/-- Complete interval computation for depth 15, residue 22952. -/
theorem bounds_15_22952 : exactInterval 15 22952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22952 : oddCount 22952 15 = 3 ∧ acceleratedOrbit 15 22952 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22952) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22952.1, data_15_22952.2]

/-- Complete interval computation for depth 15, residue 22953. -/
theorem bounds_15_22953 : exactInterval 15 22953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22953 : oddCount 22953 15 = 10 ∧ acceleratedOrbit 15 22953 = 41366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22953) = 3 ^ 10 * m + 41366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22953.1, data_15_22953.2]

/-- Complete interval computation for depth 15, residue 22954. -/
theorem bounds_15_22954 : exactInterval 15 22954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22954 : oddCount 22954 15 = 3 ∧ acceleratedOrbit 15 22954 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22954) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22954.1, data_15_22954.2]

/-- Complete interval computation for depth 15, residue 22955. -/
theorem bounds_15_22955 : exactInterval 15 22955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22955 : oddCount 22955 15 = 11 ∧ acceleratedOrbit 15 22955 = 124112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22955) = 3 ^ 11 * m + 124112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22955.1, data_15_22955.2]

/-- Complete interval computation for depth 15, residue 22956. -/
theorem bounds_15_22956 : exactInterval 15 22956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22956 : oddCount 22956 15 = 9 ∧ acceleratedOrbit 15 22956 = 13796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22956) = 3 ^ 9 * m + 13796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22956.1, data_15_22956.2]

/-- Complete interval computation for depth 15, residue 22957. -/
theorem bounds_15_22957 : exactInterval 15 22957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22957 : oddCount 22957 15 = 9 ∧ acceleratedOrbit 15 22957 = 13796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22957) = 3 ^ 9 * m + 13796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22957.1, data_15_22957.2]

/-- Complete interval computation for depth 15, residue 22958. -/
theorem bounds_15_22958 : exactInterval 15 22958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22958 : oddCount 22958 15 = 9 ∧ acceleratedOrbit 15 22958 = 13796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22958) = 3 ^ 9 * m + 13796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22958.1, data_15_22958.2]

/-- Complete interval computation for depth 15, residue 22959. -/
theorem bounds_15_22959 : exactInterval 15 22959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22959 : oddCount 22959 15 = 8 ∧ acceleratedOrbit 15 22959 = 4598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22959) = 3 ^ 8 * m + 4598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22959.1, data_15_22959.2]

/-- Complete interval computation for depth 15, residue 22960. -/
theorem bounds_15_22960 : exactInterval 15 22960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22960 : oddCount 22960 15 = 7 ∧ acceleratedOrbit 15 22960 = 1534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22960) = 3 ^ 7 * m + 1534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22960.1, data_15_22960.2]

/-- Complete interval computation for depth 15, residue 22961. -/
theorem bounds_15_22961 : exactInterval 15 22961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22961 : oddCount 22961 15 = 7 ∧ acceleratedOrbit 15 22961 = 1534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22961) = 3 ^ 7 * m + 1534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22961.1, data_15_22961.2]

/-- Complete interval computation for depth 15, residue 22962. -/
theorem bounds_15_22962 : exactInterval 15 22962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22962 : oddCount 22962 15 = 7 ∧ acceleratedOrbit 15 22962 = 1534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22962) = 3 ^ 7 * m + 1534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22962.1, data_15_22962.2]

/-- Complete interval computation for depth 15, residue 22963. -/
theorem bounds_15_22963 : exactInterval 15 22963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22963 : oddCount 22963 15 = 7 ∧ acceleratedOrbit 15 22963 = 1534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22963) = 3 ^ 7 * m + 1534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22963.1, data_15_22963.2]

/-- Complete interval computation for depth 15, residue 22964. -/
theorem bounds_15_22964 : exactInterval 15 22964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22964 : oddCount 22964 15 = 7 ∧ acceleratedOrbit 15 22964 = 1534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22964) = 3 ^ 7 * m + 1534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22964.1, data_15_22964.2]

/-- Complete interval computation for depth 15, residue 22965. -/
theorem bounds_15_22965 : exactInterval 15 22965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22965 : oddCount 22965 15 = 7 ∧ acceleratedOrbit 15 22965 = 1534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22965) = 3 ^ 7 * m + 1534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22965.1, data_15_22965.2]

/-- Complete interval computation for depth 15, residue 22966. -/
theorem bounds_15_22966 : exactInterval 15 22966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22966 : oddCount 22966 15 = 6 ∧ acceleratedOrbit 15 22966 = 511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22966) = 3 ^ 6 * m + 511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22966.1, data_15_22966.2]

/-- Complete interval computation for depth 15, residue 22967. -/
theorem bounds_15_22967 : exactInterval 15 22967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22967 : oddCount 22967 15 = 6 ∧ acceleratedOrbit 15 22967 = 511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22967) = 3 ^ 6 * m + 511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22967.1, data_15_22967.2]

/-- Complete interval computation for depth 15, residue 22968. -/
theorem bounds_15_22968 : exactInterval 15 22968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22968 : oddCount 22968 15 = 7 ∧ acceleratedOrbit 15 22968 = 1534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22968) = 3 ^ 7 * m + 1534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22968.1, data_15_22968.2]

/-- Complete interval computation for depth 15, residue 22969. -/
theorem bounds_15_22969 : exactInterval 15 22969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22969 : oddCount 22969 15 = 7 ∧ acceleratedOrbit 15 22969 = 1534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22969) = 3 ^ 7 * m + 1534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22969.1, data_15_22969.2]

end Collatz.Research.PassageAtlas.Batch0701
