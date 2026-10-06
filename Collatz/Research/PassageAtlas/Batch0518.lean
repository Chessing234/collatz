import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0518

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16941. -/
theorem bounds_15_16941 : exactInterval 15 16941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16941 : oddCount 16941 15 = 8 ∧ acceleratedOrbit 15 16941 = 3395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16941) = 3 ^ 8 * m + 3395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16941.1, data_15_16941.2]

/-- Complete interval computation for depth 15, residue 16942. -/
theorem bounds_15_16942 : exactInterval 15 16942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16942 : oddCount 16942 15 = 8 ∧ acceleratedOrbit 15 16942 = 3395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16942) = 3 ^ 8 * m + 3395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16942.1, data_15_16942.2]

/-- Complete interval computation for depth 15, residue 16943. -/
theorem bounds_15_16943 : exactInterval 15 16943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16943 : oddCount 16943 15 = 11 ∧ acceleratedOrbit 15 16943 = 91604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16943) = 3 ^ 11 * m + 91604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16943.1, data_15_16943.2]

/-- Complete interval computation for depth 15, residue 16944. -/
theorem bounds_15_16944 : exactInterval 15 16944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16944 : oddCount 16944 15 = 3 ∧ acceleratedOrbit 15 16944 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16944) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16944.1, data_15_16944.2]

/-- Complete interval computation for depth 15, residue 16945. -/
theorem bounds_15_16945 : exactInterval 15 16945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16945 : oddCount 16945 15 = 8 ∧ acceleratedOrbit 15 16945 = 3395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16945) = 3 ^ 8 * m + 3395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16945.1, data_15_16945.2]

/-- Complete interval computation for depth 15, residue 16946. -/
theorem bounds_15_16946 : exactInterval 15 16946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16946 : oddCount 16946 15 = 8 ∧ acceleratedOrbit 15 16946 = 3395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16946) = 3 ^ 8 * m + 3395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16946.1, data_15_16946.2]

/-- Complete interval computation for depth 15, residue 16947. -/
theorem bounds_15_16947 : exactInterval 15 16947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16947 : oddCount 16947 15 = 8 ∧ acceleratedOrbit 15 16947 = 3395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16947) = 3 ^ 8 * m + 3395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16947.1, data_15_16947.2]

/-- Complete interval computation for depth 15, residue 16948. -/
theorem bounds_15_16948 : exactInterval 15 16948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16948 : oddCount 16948 15 = 3 ∧ acceleratedOrbit 15 16948 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16948) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16948.1, data_15_16948.2]

/-- Complete interval computation for depth 15, residue 16949. -/
theorem bounds_15_16949 : exactInterval 15 16949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16949 : oddCount 16949 15 = 3 ∧ acceleratedOrbit 15 16949 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16949) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16949.1, data_15_16949.2]

/-- Complete interval computation for depth 15, residue 16950. -/
theorem bounds_15_16950 : exactInterval 15 16950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16950 : oddCount 16950 15 = 10 ∧ acceleratedOrbit 15 16950 = 30550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16950) = 3 ^ 10 * m + 30550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16950.1, data_15_16950.2]

/-- Complete interval computation for depth 15, residue 16951. -/
theorem bounds_15_16951 : exactInterval 15 16951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16951 : oddCount 16951 15 = 10 ∧ acceleratedOrbit 15 16951 = 30550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16951) = 3 ^ 10 * m + 30550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16951.1, data_15_16951.2]

/-- Complete interval computation for depth 15, residue 16952. -/
theorem bounds_15_16952 : exactInterval 15 16952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16952 : oddCount 16952 15 = 8 ∧ acceleratedOrbit 15 16952 = 3397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16952) = 3 ^ 8 * m + 3397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16952.1, data_15_16952.2]

/-- Complete interval computation for depth 15, residue 16953. -/
theorem bounds_15_16953 : exactInterval 15 16953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16953 : oddCount 16953 15 = 10 ∧ acceleratedOrbit 15 16953 = 30557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16953) = 3 ^ 10 * m + 30557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16953.1, data_15_16953.2]

/-- Complete interval computation for depth 15, residue 16954. -/
theorem bounds_15_16954 : exactInterval 15 16954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16954 : oddCount 16954 15 = 8 ∧ acceleratedOrbit 15 16954 = 3397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16954) = 3 ^ 8 * m + 3397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16954.1, data_15_16954.2]

/-- Complete interval computation for depth 15, residue 16955. -/
theorem bounds_15_16955 : exactInterval 15 16955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16955 : oddCount 16955 15 = 7 ∧ acceleratedOrbit 15 16955 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16955) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16955.1, data_15_16955.2]

/-- Complete interval computation for depth 15, residue 16956. -/
theorem bounds_15_16956 : exactInterval 15 16956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16956 : oddCount 16956 15 = 8 ∧ acceleratedOrbit 15 16956 = 3397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16956) = 3 ^ 8 * m + 3397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16956.1, data_15_16956.2]

/-- Complete interval computation for depth 15, residue 16957. -/
theorem bounds_15_16957 : exactInterval 15 16957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16957 : oddCount 16957 15 = 8 ∧ acceleratedOrbit 15 16957 = 3397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16957) = 3 ^ 8 * m + 3397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16957.1, data_15_16957.2]

/-- Complete interval computation for depth 15, residue 16958. -/
theorem bounds_15_16958 : exactInterval 15 16958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16958 : oddCount 16958 15 = 7 ∧ acceleratedOrbit 15 16958 = 1132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16958) = 3 ^ 7 * m + 1132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16958.1, data_15_16958.2]

/-- Complete interval computation for depth 15, residue 16959. -/
theorem bounds_15_16959 : exactInterval 15 16959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16959 : oddCount 16959 15 = 7 ∧ acceleratedOrbit 15 16959 = 1132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16959) = 3 ^ 7 * m + 1132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16959.1, data_15_16959.2]

/-- Complete interval computation for depth 15, residue 16960. -/
theorem bounds_15_16960 : exactInterval 15 16960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16960 : oddCount 16960 15 = 6 ∧ acceleratedOrbit 15 16960 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16960) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16960.1, data_15_16960.2]

/-- Complete interval computation for depth 15, residue 16961. -/
theorem bounds_15_16961 : exactInterval 15 16961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16961 : oddCount 16961 15 = 8 ∧ acceleratedOrbit 15 16961 = 3401 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16961) = 3 ^ 8 * m + 3401 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16961.1, data_15_16961.2]

/-- Complete interval computation for depth 15, residue 16962. -/
theorem bounds_15_16962 : exactInterval 15 16962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16962 : oddCount 16962 15 = 8 ∧ acceleratedOrbit 15 16962 = 3401 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16962) = 3 ^ 8 * m + 3401 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16962.1, data_15_16962.2]

/-- Complete interval computation for depth 15, residue 16963. -/
theorem bounds_15_16963 : exactInterval 15 16963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16963 : oddCount 16963 15 = 8 ∧ acceleratedOrbit 15 16963 = 3401 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16963) = 3 ^ 8 * m + 3401 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16963.1, data_15_16963.2]

/-- Complete interval computation for depth 15, residue 16964. -/
theorem bounds_15_16964 : exactInterval 15 16964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16964 : oddCount 16964 15 = 9 ∧ acceleratedOrbit 15 16964 = 10205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16964) = 3 ^ 9 * m + 10205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16964.1, data_15_16964.2]

/-- Complete interval computation for depth 15, residue 16965. -/
theorem bounds_15_16965 : exactInterval 15 16965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16965 : oddCount 16965 15 = 9 ∧ acceleratedOrbit 15 16965 = 10205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16965) = 3 ^ 9 * m + 10205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16965.1, data_15_16965.2]

/-- Complete interval computation for depth 15, residue 16966. -/
theorem bounds_15_16966 : exactInterval 15 16966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16966 : oddCount 16966 15 = 9 ∧ acceleratedOrbit 15 16966 = 10205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16966) = 3 ^ 9 * m + 10205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16966.1, data_15_16966.2]

/-- Complete interval computation for depth 15, residue 16967. -/
theorem bounds_15_16967 : exactInterval 15 16967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16967 : oddCount 16967 15 = 7 ∧ acceleratedOrbit 15 16967 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16967) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16967.1, data_15_16967.2]

/-- Complete interval computation for depth 15, residue 16968. -/
theorem bounds_15_16968 : exactInterval 15 16968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16968 : oddCount 16968 15 = 9 ∧ acceleratedOrbit 15 16968 = 10205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16968) = 3 ^ 9 * m + 10205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16968.1, data_15_16968.2]

/-- Complete interval computation for depth 15, residue 16969. -/
theorem bounds_15_16969 : exactInterval 15 16969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16969 : oddCount 16969 15 = 9 ∧ acceleratedOrbit 15 16969 = 10196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16969) = 3 ^ 9 * m + 10196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16969.1, data_15_16969.2]

/-- Complete interval computation for depth 15, residue 16970. -/
theorem bounds_15_16970 : exactInterval 15 16970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16970 : oddCount 16970 15 = 9 ∧ acceleratedOrbit 15 16970 = 10205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16970) = 3 ^ 9 * m + 10205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16970.1, data_15_16970.2]

/-- Complete interval computation for depth 15, residue 16971. -/
theorem bounds_15_16971 : exactInterval 15 16971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16971 : oddCount 16971 15 = 9 ∧ acceleratedOrbit 15 16971 = 10205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16971) = 3 ^ 9 * m + 10205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16971.1, data_15_16971.2]

/-- Complete interval computation for depth 15, residue 16972. -/
theorem bounds_15_16972 : exactInterval 15 16972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16972 : oddCount 16972 15 = 9 ∧ acceleratedOrbit 15 16972 = 10205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16972) = 3 ^ 9 * m + 10205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16972.1, data_15_16972.2]

end Collatz.Research.PassageAtlas.Batch0518
