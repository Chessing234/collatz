import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0457

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14942. -/
theorem bounds_15_14942 : exactInterval 15 14942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14942 : oddCount 14942 15 = 10 ∧ acceleratedOrbit 15 14942 = 26932 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14942) = 3 ^ 10 * m + 26932 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14942.1, data_15_14942.2]

/-- Complete interval computation for depth 15, residue 14943. -/
theorem bounds_15_14943 : exactInterval 15 14943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14943 : oddCount 14943 15 = 10 ∧ acceleratedOrbit 15 14943 = 26932 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14943) = 3 ^ 10 * m + 26932 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14943.1, data_15_14943.2]

/-- Complete interval computation for depth 15, residue 14944. -/
theorem bounds_15_14944 : exactInterval 15 14944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14944 : oddCount 14944 15 = 6 ∧ acceleratedOrbit 15 14944 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14944) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14944.1, data_15_14944.2]

/-- Complete interval computation for depth 15, residue 14945. -/
theorem bounds_15_14945 : exactInterval 15 14945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14945 : oddCount 14945 15 = 9 ∧ acceleratedOrbit 15 14945 = 8981 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14945) = 3 ^ 9 * m + 8981 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14945.1, data_15_14945.2]

/-- Complete interval computation for depth 15, residue 14946. -/
theorem bounds_15_14946 : exactInterval 15 14946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14946 : oddCount 14946 15 = 9 ∧ acceleratedOrbit 15 14946 = 8990 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14946) = 3 ^ 9 * m + 8990 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14946.1, data_15_14946.2]

/-- Complete interval computation for depth 15, residue 14947. -/
theorem bounds_15_14947 : exactInterval 15 14947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14947 : oddCount 14947 15 = 9 ∧ acceleratedOrbit 15 14947 = 8990 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14947) = 3 ^ 9 * m + 8990 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14947.1, data_15_14947.2]

/-- Complete interval computation for depth 15, residue 14948. -/
theorem bounds_15_14948 : exactInterval 15 14948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14948 : oddCount 14948 15 = 9 ∧ acceleratedOrbit 15 14948 = 8990 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14948) = 3 ^ 9 * m + 8990 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14948.1, data_15_14948.2]

/-- Complete interval computation for depth 15, residue 14949. -/
theorem bounds_15_14949 : exactInterval 15 14949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14949 : oddCount 14949 15 = 9 ∧ acceleratedOrbit 15 14949 = 8990 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14949) = 3 ^ 9 * m + 8990 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14949.1, data_15_14949.2]

/-- Complete interval computation for depth 15, residue 14950. -/
theorem bounds_15_14950 : exactInterval 15 14950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14950 : oddCount 14950 15 = 9 ∧ acceleratedOrbit 15 14950 = 8990 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14950) = 3 ^ 9 * m + 8990 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14950.1, data_15_14950.2]

/-- Complete interval computation for depth 15, residue 14951. -/
theorem bounds_15_14951 : exactInterval 15 14951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14951 : oddCount 14951 15 = 11 ∧ acceleratedOrbit 15 14951 = 80837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14951) = 3 ^ 11 * m + 80837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14951.1, data_15_14951.2]

/-- Complete interval computation for depth 15, residue 14952. -/
theorem bounds_15_14952 : exactInterval 15 14952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14952 : oddCount 14952 15 = 6 ∧ acceleratedOrbit 15 14952 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14952) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14952.1, data_15_14952.2]

/-- Complete interval computation for depth 15, residue 14953. -/
theorem bounds_15_14953 : exactInterval 15 14953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14953 : oddCount 14953 15 = 9 ∧ acceleratedOrbit 15 14953 = 8984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14953) = 3 ^ 9 * m + 8984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14953.1, data_15_14953.2]

/-- Complete interval computation for depth 15, residue 14954. -/
theorem bounds_15_14954 : exactInterval 15 14954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14954 : oddCount 14954 15 = 6 ∧ acceleratedOrbit 15 14954 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14954) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14954.1, data_15_14954.2]

/-- Complete interval computation for depth 15, residue 14955. -/
theorem bounds_15_14955 : exactInterval 15 14955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14955 : oddCount 14955 15 = 8 ∧ acceleratedOrbit 15 14955 = 2996 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14955) = 3 ^ 8 * m + 2996 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14955.1, data_15_14955.2]

/-- Complete interval computation for depth 15, residue 14956. -/
theorem bounds_15_14956 : exactInterval 15 14956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14956 : oddCount 14956 15 = 10 ∧ acceleratedOrbit 15 14956 = 26963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14956) = 3 ^ 10 * m + 26963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14956.1, data_15_14956.2]

/-- Complete interval computation for depth 15, residue 14957. -/
theorem bounds_15_14957 : exactInterval 15 14957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14957 : oddCount 14957 15 = 10 ∧ acceleratedOrbit 15 14957 = 26963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14957) = 3 ^ 10 * m + 26963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14957.1, data_15_14957.2]

/-- Complete interval computation for depth 15, residue 14958. -/
theorem bounds_15_14958 : exactInterval 15 14958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14958 : oddCount 14958 15 = 10 ∧ acceleratedOrbit 15 14958 = 26963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14958) = 3 ^ 10 * m + 26963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14958.1, data_15_14958.2]

/-- Complete interval computation for depth 15, residue 14959. -/
theorem bounds_15_14959 : exactInterval 15 14959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14959 : oddCount 14959 15 = 11 ∧ acceleratedOrbit 15 14959 = 80878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14959) = 3 ^ 11 * m + 80878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14959.1, data_15_14959.2]

/-- Complete interval computation for depth 15, residue 14960. -/
theorem bounds_15_14960 : exactInterval 15 14960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14960 : oddCount 14960 15 = 7 ∧ acceleratedOrbit 15 14960 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14960) = 3 ^ 7 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14960.1, data_15_14960.2]

/-- Complete interval computation for depth 15, residue 14961. -/
theorem bounds_15_14961 : exactInterval 15 14961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14961 : oddCount 14961 15 = 6 ∧ acceleratedOrbit 15 14961 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14961) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14961.1, data_15_14961.2]

/-- Complete interval computation for depth 15, residue 14962. -/
theorem bounds_15_14962 : exactInterval 15 14962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14962 : oddCount 14962 15 = 11 ∧ acceleratedOrbit 15 14962 = 80918 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14962) = 3 ^ 11 * m + 80918 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14962.1, data_15_14962.2]

/-- Complete interval computation for depth 15, residue 14963. -/
theorem bounds_15_14963 : exactInterval 15 14963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14963 : oddCount 14963 15 = 11 ∧ acceleratedOrbit 15 14963 = 80918 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14963) = 3 ^ 11 * m + 80918 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14963.1, data_15_14963.2]

/-- Complete interval computation for depth 15, residue 14964. -/
theorem bounds_15_14964 : exactInterval 15 14964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14964 : oddCount 14964 15 = 7 ∧ acceleratedOrbit 15 14964 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14964) = 3 ^ 7 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14964.1, data_15_14964.2]

/-- Complete interval computation for depth 15, residue 14965. -/
theorem bounds_15_14965 : exactInterval 15 14965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14965 : oddCount 14965 15 = 7 ∧ acceleratedOrbit 15 14965 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14965) = 3 ^ 7 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14965.1, data_15_14965.2]

/-- Complete interval computation for depth 15, residue 14966. -/
theorem bounds_15_14966 : exactInterval 15 14966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14966 : oddCount 14966 15 = 4 ∧ acceleratedOrbit 15 14966 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14966) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14966.1, data_15_14966.2]

/-- Complete interval computation for depth 15, residue 14967. -/
theorem bounds_15_14967 : exactInterval 15 14967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14967 : oddCount 14967 15 = 4 ∧ acceleratedOrbit 15 14967 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14967) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14967.1, data_15_14967.2]

/-- Complete interval computation for depth 15, residue 14968. -/
theorem bounds_15_14968 : exactInterval 15 14968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14968 : oddCount 14968 15 = 7 ∧ acceleratedOrbit 15 14968 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14968) = 3 ^ 7 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14968.1, data_15_14968.2]

/-- Complete interval computation for depth 15, residue 14969. -/
theorem bounds_15_14969 : exactInterval 15 14969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14969 : oddCount 14969 15 = 8 ∧ acceleratedOrbit 15 14969 = 2998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14969) = 3 ^ 8 * m + 2998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14969.1, data_15_14969.2]

/-- Complete interval computation for depth 15, residue 14970. -/
theorem bounds_15_14970 : exactInterval 15 14970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14970 : oddCount 14970 15 = 7 ∧ acceleratedOrbit 15 14970 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14970) = 3 ^ 7 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14970.1, data_15_14970.2]

/-- Complete interval computation for depth 15, residue 14971. -/
theorem bounds_15_14971 : exactInterval 15 14971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14971 : oddCount 14971 15 = 8 ∧ acceleratedOrbit 15 14971 = 2999 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14971) = 3 ^ 8 * m + 2999 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14971.1, data_15_14971.2]

/-- Complete interval computation for depth 15, residue 14972. -/
theorem bounds_15_14972 : exactInterval 15 14972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14972 : oddCount 14972 15 = 9 ∧ acceleratedOrbit 15 14972 = 8996 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14972) = 3 ^ 9 * m + 8996 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14972.1, data_15_14972.2]

/-- Complete interval computation for depth 15, residue 14973. -/
theorem bounds_15_14973 : exactInterval 15 14973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14973 : oddCount 14973 15 = 9 ∧ acceleratedOrbit 15 14973 = 8996 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14973) = 3 ^ 9 * m + 8996 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14973.1, data_15_14973.2]

end Collatz.Research.PassageAtlas.Batch0457
