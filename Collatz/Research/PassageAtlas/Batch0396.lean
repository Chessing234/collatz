import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0396

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12943. -/
theorem bounds_15_12943 : exactInterval 15 12943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12943 : oddCount 12943 15 = 12 ∧ acceleratedOrbit 15 12943 = 209951 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12943) = 3 ^ 12 * m + 209951 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12943.1, data_15_12943.2]

/-- Complete interval computation for depth 15, residue 12944. -/
theorem bounds_15_12944 : exactInterval 15 12944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12944 : oddCount 12944 15 = 7 ∧ acceleratedOrbit 15 12944 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12944) = 3 ^ 7 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12944.1, data_15_12944.2]

/-- Complete interval computation for depth 15, residue 12945. -/
theorem bounds_15_12945 : exactInterval 15 12945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12945 : oddCount 12945 15 = 8 ∧ acceleratedOrbit 15 12945 = 2594 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12945) = 3 ^ 8 * m + 2594 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12945.1, data_15_12945.2]

/-- Complete interval computation for depth 15, residue 12946. -/
theorem bounds_15_12946 : exactInterval 15 12946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12946 : oddCount 12946 15 = 8 ∧ acceleratedOrbit 15 12946 = 2594 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12946) = 3 ^ 8 * m + 2594 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12946.1, data_15_12946.2]

/-- Complete interval computation for depth 15, residue 12947. -/
theorem bounds_15_12947 : exactInterval 15 12947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12947 : oddCount 12947 15 = 8 ∧ acceleratedOrbit 15 12947 = 2594 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12947) = 3 ^ 8 * m + 2594 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12947.1, data_15_12947.2]

/-- Complete interval computation for depth 15, residue 12948. -/
theorem bounds_15_12948 : exactInterval 15 12948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12948 : oddCount 12948 15 = 7 ∧ acceleratedOrbit 15 12948 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12948) = 3 ^ 7 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12948.1, data_15_12948.2]

/-- Complete interval computation for depth 15, residue 12949. -/
theorem bounds_15_12949 : exactInterval 15 12949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12949 : oddCount 12949 15 = 7 ∧ acceleratedOrbit 15 12949 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12949) = 3 ^ 7 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12949.1, data_15_12949.2]

/-- Complete interval computation for depth 15, residue 12950. -/
theorem bounds_15_12950 : exactInterval 15 12950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12950 : oddCount 12950 15 = 7 ∧ acceleratedOrbit 15 12950 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12950) = 3 ^ 7 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12950.1, data_15_12950.2]

/-- Complete interval computation for depth 15, residue 12951. -/
theorem bounds_15_12951 : exactInterval 15 12951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12951 : oddCount 12951 15 = 7 ∧ acceleratedOrbit 15 12951 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12951) = 3 ^ 7 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12951.1, data_15_12951.2]

/-- Complete interval computation for depth 15, residue 12952. -/
theorem bounds_15_12952 : exactInterval 15 12952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12952 : oddCount 12952 15 = 7 ∧ acceleratedOrbit 15 12952 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12952) = 3 ^ 7 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12952.1, data_15_12952.2]

/-- Complete interval computation for depth 15, residue 12953. -/
theorem bounds_15_12953 : exactInterval 15 12953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12953 : oddCount 12953 15 = 7 ∧ acceleratedOrbit 15 12953 = 865 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12953) = 3 ^ 7 * m + 865 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12953.1, data_15_12953.2]

/-- Complete interval computation for depth 15, residue 12954. -/
theorem bounds_15_12954 : exactInterval 15 12954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12954 : oddCount 12954 15 = 7 ∧ acceleratedOrbit 15 12954 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12954) = 3 ^ 7 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12954.1, data_15_12954.2]

/-- Complete interval computation for depth 15, residue 12955. -/
theorem bounds_15_12955 : exactInterval 15 12955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12955 : oddCount 12955 15 = 12 ∧ acceleratedOrbit 15 12955 = 210134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12955) = 3 ^ 12 * m + 210134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12955.1, data_15_12955.2]

/-- Complete interval computation for depth 15, residue 12956. -/
theorem bounds_15_12956 : exactInterval 15 12956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12956 : oddCount 12956 15 = 9 ∧ acceleratedOrbit 15 12956 = 7786 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12956) = 3 ^ 9 * m + 7786 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12956.1, data_15_12956.2]

/-- Complete interval computation for depth 15, residue 12957. -/
theorem bounds_15_12957 : exactInterval 15 12957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12957 : oddCount 12957 15 = 9 ∧ acceleratedOrbit 15 12957 = 7786 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12957) = 3 ^ 9 * m + 7786 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12957.1, data_15_12957.2]

/-- Complete interval computation for depth 15, residue 12958. -/
theorem bounds_15_12958 : exactInterval 15 12958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12958 : oddCount 12958 15 = 9 ∧ acceleratedOrbit 15 12958 = 7786 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12958) = 3 ^ 9 * m + 7786 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12958.1, data_15_12958.2]

/-- Complete interval computation for depth 15, residue 12959. -/
theorem bounds_15_12959 : exactInterval 15 12959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12959 : oddCount 12959 15 = 12 ∧ acceleratedOrbit 15 12959 = 210194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12959) = 3 ^ 12 * m + 210194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12959.1, data_15_12959.2]

/-- Complete interval computation for depth 15, residue 12960. -/
theorem bounds_15_12960 : exactInterval 15 12960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12960 : oddCount 12960 15 = 3 ∧ acceleratedOrbit 15 12960 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12960) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12960.1, data_15_12960.2]

/-- Complete interval computation for depth 15, residue 12961. -/
theorem bounds_15_12961 : exactInterval 15 12961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12961 : oddCount 12961 15 = 8 ∧ acceleratedOrbit 15 12961 = 2596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12961) = 3 ^ 8 * m + 2596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12961.1, data_15_12961.2]

/-- Complete interval computation for depth 15, residue 12962. -/
theorem bounds_15_12962 : exactInterval 15 12962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12962 : oddCount 12962 15 = 8 ∧ acceleratedOrbit 15 12962 = 2597 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12962) = 3 ^ 8 * m + 2597 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12962.1, data_15_12962.2]

/-- Complete interval computation for depth 15, residue 12963. -/
theorem bounds_15_12963 : exactInterval 15 12963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12963 : oddCount 12963 15 = 8 ∧ acceleratedOrbit 15 12963 = 2597 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12963) = 3 ^ 8 * m + 2597 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12963.1, data_15_12963.2]

/-- Complete interval computation for depth 15, residue 12964. -/
theorem bounds_15_12964 : exactInterval 15 12964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12964 : oddCount 12964 15 = 8 ∧ acceleratedOrbit 15 12964 = 2597 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12964) = 3 ^ 8 * m + 2597 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12964.1, data_15_12964.2]

/-- Complete interval computation for depth 15, residue 12965. -/
theorem bounds_15_12965 : exactInterval 15 12965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12965 : oddCount 12965 15 = 8 ∧ acceleratedOrbit 15 12965 = 2597 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12965) = 3 ^ 8 * m + 2597 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12965.1, data_15_12965.2]

/-- Complete interval computation for depth 15, residue 12966. -/
theorem bounds_15_12966 : exactInterval 15 12966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12966 : oddCount 12966 15 = 8 ∧ acceleratedOrbit 15 12966 = 2597 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12966) = 3 ^ 8 * m + 2597 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12966.1, data_15_12966.2]

/-- Complete interval computation for depth 15, residue 12967. -/
theorem bounds_15_12967 : exactInterval 15 12967 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12967) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12967 : oddCount 12967 15 = 9 ∧ acceleratedOrbit 15 12967 = 7790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12967) = 3 ^ 9 * m + 7790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12967.1, data_15_12967.2]

/-- Complete interval computation for depth 15, residue 12968. -/
theorem bounds_15_12968 : exactInterval 15 12968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12968 : oddCount 12968 15 = 3 ∧ acceleratedOrbit 15 12968 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12968) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12968.1, data_15_12968.2]

/-- Complete interval computation for depth 15, residue 12969. -/
theorem bounds_15_12969 : exactInterval 15 12969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12969 : oddCount 12969 15 = 11 ∧ acceleratedOrbit 15 12969 = 70121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12969) = 3 ^ 11 * m + 70121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12969.1, data_15_12969.2]

/-- Complete interval computation for depth 15, residue 12970. -/
theorem bounds_15_12970 : exactInterval 15 12970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12970 : oddCount 12970 15 = 3 ∧ acceleratedOrbit 15 12970 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12970) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12970.1, data_15_12970.2]

/-- Complete interval computation for depth 15, residue 12971. -/
theorem bounds_15_12971 : exactInterval 15 12971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12971 : oddCount 12971 15 = 7 ∧ acceleratedOrbit 15 12971 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12971) = 3 ^ 7 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12971.1, data_15_12971.2]

/-- Complete interval computation for depth 15, residue 12972. -/
theorem bounds_15_12972 : exactInterval 15 12972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12972 : oddCount 12972 15 = 6 ∧ acceleratedOrbit 15 12972 = 289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12972) = 3 ^ 6 * m + 289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12972.1, data_15_12972.2]

/-- Complete interval computation for depth 15, residue 12973. -/
theorem bounds_15_12973 : exactInterval 15 12973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12973 : oddCount 12973 15 = 6 ∧ acceleratedOrbit 15 12973 = 289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12973) = 3 ^ 6 * m + 289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12973.1, data_15_12973.2]

/-- Complete interval computation for depth 15, residue 12974. -/
theorem bounds_15_12974 : exactInterval 15 12974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12974 : oddCount 12974 15 = 6 ∧ acceleratedOrbit 15 12974 = 289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12974) = 3 ^ 6 * m + 289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12974.1, data_15_12974.2]

/-- Complete interval computation for depth 15, residue 12975. -/
theorem bounds_15_12975 : exactInterval 15 12975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12975 : oddCount 12975 15 = 9 ∧ acceleratedOrbit 15 12975 = 7796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12975) = 3 ^ 9 * m + 7796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12975.1, data_15_12975.2]

end Collatz.Research.PassageAtlas.Batch0396
