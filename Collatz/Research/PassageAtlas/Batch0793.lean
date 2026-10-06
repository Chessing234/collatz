import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0793

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25952. -/
theorem bounds_15_25952 : exactInterval 15 25952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25952 : oddCount 25952 15 = 5 ∧ acceleratedOrbit 15 25952 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25952) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25952.1, data_15_25952.2]

/-- Complete interval computation for depth 15, residue 25953. -/
theorem bounds_15_25953 : exactInterval 15 25953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25953 : oddCount 25953 15 = 9 ∧ acceleratedOrbit 15 25953 = 15592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25953) = 3 ^ 9 * m + 15592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25953.1, data_15_25953.2]

/-- Complete interval computation for depth 15, residue 25954. -/
theorem bounds_15_25954 : exactInterval 15 25954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25954 : oddCount 25954 15 = 6 ∧ acceleratedOrbit 15 25954 = 578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25954) = 3 ^ 6 * m + 578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25954.1, data_15_25954.2]

/-- Complete interval computation for depth 15, residue 25955. -/
theorem bounds_15_25955 : exactInterval 15 25955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25955 : oddCount 25955 15 = 6 ∧ acceleratedOrbit 15 25955 = 578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25955) = 3 ^ 6 * m + 578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25955.1, data_15_25955.2]

/-- Complete interval computation for depth 15, residue 25956. -/
theorem bounds_15_25956 : exactInterval 15 25956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25956 : oddCount 25956 15 = 6 ∧ acceleratedOrbit 15 25956 = 578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25956) = 3 ^ 6 * m + 578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25956.1, data_15_25956.2]

/-- Complete interval computation for depth 15, residue 25957. -/
theorem bounds_15_25957 : exactInterval 15 25957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25957 : oddCount 25957 15 = 6 ∧ acceleratedOrbit 15 25957 = 578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25957) = 3 ^ 6 * m + 578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25957.1, data_15_25957.2]

/-- Complete interval computation for depth 15, residue 25958. -/
theorem bounds_15_25958 : exactInterval 15 25958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25958 : oddCount 25958 15 = 6 ∧ acceleratedOrbit 15 25958 = 578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25958) = 3 ^ 6 * m + 578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25958.1, data_15_25958.2]

/-- Complete interval computation for depth 15, residue 25959. -/
theorem bounds_15_25959 : exactInterval 15 25959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25959 : oddCount 25959 15 = 11 ∧ acceleratedOrbit 15 25959 = 140345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25959) = 3 ^ 11 * m + 140345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25959.1, data_15_25959.2]

/-- Complete interval computation for depth 15, residue 25960. -/
theorem bounds_15_25960 : exactInterval 15 25960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25960 : oddCount 25960 15 = 5 ∧ acceleratedOrbit 15 25960 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25960) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25960.1, data_15_25960.2]

/-- Complete interval computation for depth 15, residue 25961. -/
theorem bounds_15_25961 : exactInterval 15 25961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25961 : oddCount 25961 15 = 7 ∧ acceleratedOrbit 15 25961 = 1733 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25961) = 3 ^ 7 * m + 1733 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25961.1, data_15_25961.2]

/-- Complete interval computation for depth 15, residue 25962. -/
theorem bounds_15_25962 : exactInterval 15 25962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25962 : oddCount 25962 15 = 5 ∧ acceleratedOrbit 15 25962 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25962) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25962.1, data_15_25962.2]

/-- Complete interval computation for depth 15, residue 25963. -/
theorem bounds_15_25963 : exactInterval 15 25963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25963 : oddCount 25963 15 = 7 ∧ acceleratedOrbit 15 25963 = 1733 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25963) = 3 ^ 7 * m + 1733 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25963.1, data_15_25963.2]

/-- Complete interval computation for depth 15, residue 25964. -/
theorem bounds_15_25964 : exactInterval 15 25964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25964 : oddCount 25964 15 = 8 ∧ acceleratedOrbit 15 25964 = 5201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25964) = 3 ^ 8 * m + 5201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25964.1, data_15_25964.2]

/-- Complete interval computation for depth 15, residue 25965. -/
theorem bounds_15_25965 : exactInterval 15 25965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25965 : oddCount 25965 15 = 8 ∧ acceleratedOrbit 15 25965 = 5201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25965) = 3 ^ 8 * m + 5201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25965.1, data_15_25965.2]

/-- Complete interval computation for depth 15, residue 25966. -/
theorem bounds_15_25966 : exactInterval 15 25966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25966 : oddCount 25966 15 = 8 ∧ acceleratedOrbit 15 25966 = 5201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25966) = 3 ^ 8 * m + 5201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25966.1, data_15_25966.2]

/-- Complete interval computation for depth 15, residue 25967. -/
theorem bounds_15_25967 : exactInterval 15 25967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25967 : oddCount 25967 15 = 9 ∧ acceleratedOrbit 15 25967 = 15599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25967) = 3 ^ 9 * m + 15599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25967.1, data_15_25967.2]

/-- Complete interval computation for depth 15, residue 25968. -/
theorem bounds_15_25968 : exactInterval 15 25968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25968 : oddCount 25968 15 = 5 ∧ acceleratedOrbit 15 25968 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25968) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25968.1, data_15_25968.2]

/-- Complete interval computation for depth 15, residue 25969. -/
theorem bounds_15_25969 : exactInterval 15 25969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25969 : oddCount 25969 15 = 5 ∧ acceleratedOrbit 15 25969 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25969) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25969.1, data_15_25969.2]

/-- Complete interval computation for depth 15, residue 25970. -/
theorem bounds_15_25970 : exactInterval 15 25970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25970 : oddCount 25970 15 = 6 ∧ acceleratedOrbit 15 25970 = 578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25970) = 3 ^ 6 * m + 578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25970.1, data_15_25970.2]

/-- Complete interval computation for depth 15, residue 25971. -/
theorem bounds_15_25971 : exactInterval 15 25971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25971 : oddCount 25971 15 = 6 ∧ acceleratedOrbit 15 25971 = 578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25971) = 3 ^ 6 * m + 578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25971.1, data_15_25971.2]

/-- Complete interval computation for depth 15, residue 25972. -/
theorem bounds_15_25972 : exactInterval 15 25972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25972 : oddCount 25972 15 = 5 ∧ acceleratedOrbit 15 25972 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25972) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25972.1, data_15_25972.2]

/-- Complete interval computation for depth 15, residue 25973. -/
theorem bounds_15_25973 : exactInterval 15 25973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25973 : oddCount 25973 15 = 5 ∧ acceleratedOrbit 15 25973 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25973) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25973.1, data_15_25973.2]

/-- Complete interval computation for depth 15, residue 25974. -/
theorem bounds_15_25974 : exactInterval 15 25974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25974 : oddCount 25974 15 = 10 ∧ acceleratedOrbit 15 25974 = 46817 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25974) = 3 ^ 10 * m + 46817 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25974.1, data_15_25974.2]

/-- Complete interval computation for depth 15, residue 25975. -/
theorem bounds_15_25975 : exactInterval 15 25975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25975 : oddCount 25975 15 = 10 ∧ acceleratedOrbit 15 25975 = 46817 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25975) = 3 ^ 10 * m + 46817 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25975.1, data_15_25975.2]

/-- Complete interval computation for depth 15, residue 25976. -/
theorem bounds_15_25976 : exactInterval 15 25976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25976 : oddCount 25976 15 = 8 ∧ acceleratedOrbit 15 25976 = 5204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25976) = 3 ^ 8 * m + 5204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25976.1, data_15_25976.2]

/-- Complete interval computation for depth 15, residue 25977. -/
theorem bounds_15_25977 : exactInterval 15 25977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25977 : oddCount 25977 15 = 11 ∧ acceleratedOrbit 15 25977 = 140447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25977) = 3 ^ 11 * m + 140447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25977.1, data_15_25977.2]

/-- Complete interval computation for depth 15, residue 25978. -/
theorem bounds_15_25978 : exactInterval 15 25978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25978 : oddCount 25978 15 = 8 ∧ acceleratedOrbit 15 25978 = 5204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25978) = 3 ^ 8 * m + 5204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25978.1, data_15_25978.2]

/-- Complete interval computation for depth 15, residue 25979. -/
theorem bounds_15_25979 : exactInterval 15 25979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25979 : oddCount 25979 15 = 6 ∧ acceleratedOrbit 15 25979 = 578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25979) = 3 ^ 6 * m + 578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25979.1, data_15_25979.2]

/-- Complete interval computation for depth 15, residue 25980. -/
theorem bounds_15_25980 : exactInterval 15 25980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25980 : oddCount 25980 15 = 8 ∧ acceleratedOrbit 15 25980 = 5204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25980) = 3 ^ 8 * m + 5204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25980.1, data_15_25980.2]

/-- Complete interval computation for depth 15, residue 25981. -/
theorem bounds_15_25981 : exactInterval 15 25981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25981 : oddCount 25981 15 = 8 ∧ acceleratedOrbit 15 25981 = 5204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25981) = 3 ^ 8 * m + 5204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25981.1, data_15_25981.2]

/-- Complete interval computation for depth 15, residue 25982. -/
theorem bounds_15_25982 : exactInterval 15 25982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25982 : oddCount 25982 15 = 11 ∧ acceleratedOrbit 15 25982 = 140474 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25982) = 3 ^ 11 * m + 140474 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25982.1, data_15_25982.2]

/-- Complete interval computation for depth 15, residue 25983. -/
theorem bounds_15_25983 : exactInterval 15 25983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25983 : oddCount 25983 15 = 11 ∧ acceleratedOrbit 15 25983 = 140474 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25983) = 3 ^ 11 * m + 140474 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25983.1, data_15_25983.2]

/-- Complete interval computation for depth 15, residue 25984. -/
theorem bounds_15_25984 : exactInterval 15 25984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25984 : oddCount 25984 15 = 4 ∧ acceleratedOrbit 15 25984 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25984) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25984.1, data_15_25984.2]

end Collatz.Research.PassageAtlas.Batch0793
