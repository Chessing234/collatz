import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0854

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27951. -/
theorem bounds_15_27951 : exactInterval 15 27951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27951 : oddCount 27951 15 = 10 ∧ acceleratedOrbit 15 27951 = 50372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27951) = 3 ^ 10 * m + 50372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27951.1, data_15_27951.2]

/-- Complete interval computation for depth 15, residue 27952. -/
theorem bounds_15_27952 : exactInterval 15 27952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27952 : oddCount 27952 15 = 6 ∧ acceleratedOrbit 15 27952 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27952) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27952.1, data_15_27952.2]

/-- Complete interval computation for depth 15, residue 27953. -/
theorem bounds_15_27953 : exactInterval 15 27953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27953 : oddCount 27953 15 = 8 ∧ acceleratedOrbit 15 27953 = 5599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27953) = 3 ^ 8 * m + 5599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27953.1, data_15_27953.2]

/-- Complete interval computation for depth 15, residue 27954. -/
theorem bounds_15_27954 : exactInterval 15 27954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27954 : oddCount 27954 15 = 8 ∧ acceleratedOrbit 15 27954 = 5599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27954) = 3 ^ 8 * m + 5599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27954.1, data_15_27954.2]

/-- Complete interval computation for depth 15, residue 27955. -/
theorem bounds_15_27955 : exactInterval 15 27955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27955 : oddCount 27955 15 = 8 ∧ acceleratedOrbit 15 27955 = 5599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27955) = 3 ^ 8 * m + 5599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27955.1, data_15_27955.2]

/-- Complete interval computation for depth 15, residue 27956. -/
theorem bounds_15_27956 : exactInterval 15 27956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27956 : oddCount 27956 15 = 6 ∧ acceleratedOrbit 15 27956 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27956) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27956.1, data_15_27956.2]

/-- Complete interval computation for depth 15, residue 27957. -/
theorem bounds_15_27957 : exactInterval 15 27957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27957 : oddCount 27957 15 = 6 ∧ acceleratedOrbit 15 27957 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27957) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27957.1, data_15_27957.2]

/-- Complete interval computation for depth 15, residue 27958. -/
theorem bounds_15_27958 : exactInterval 15 27958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27958 : oddCount 27958 15 = 9 ∧ acceleratedOrbit 15 27958 = 16796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27958) = 3 ^ 9 * m + 16796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27958.1, data_15_27958.2]

/-- Complete interval computation for depth 15, residue 27959. -/
theorem bounds_15_27959 : exactInterval 15 27959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27959 : oddCount 27959 15 = 9 ∧ acceleratedOrbit 15 27959 = 16796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27959) = 3 ^ 9 * m + 16796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27959.1, data_15_27959.2]

/-- Complete interval computation for depth 15, residue 27960. -/
theorem bounds_15_27960 : exactInterval 15 27960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27960 : oddCount 27960 15 = 7 ∧ acceleratedOrbit 15 27960 = 1867 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27960) = 3 ^ 7 * m + 1867 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27960.1, data_15_27960.2]

/-- Complete interval computation for depth 15, residue 27961. -/
theorem bounds_15_27961 : exactInterval 15 27961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27961 : oddCount 27961 15 = 10 ∧ acceleratedOrbit 15 27961 = 50392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27961) = 3 ^ 10 * m + 50392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27961.1, data_15_27961.2]

/-- Complete interval computation for depth 15, residue 27962. -/
theorem bounds_15_27962 : exactInterval 15 27962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27962 : oddCount 27962 15 = 7 ∧ acceleratedOrbit 15 27962 = 1867 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27962) = 3 ^ 7 * m + 1867 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27962.1, data_15_27962.2]

/-- Complete interval computation for depth 15, residue 27963. -/
theorem bounds_15_27963 : exactInterval 15 27963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27963 : oddCount 27963 15 = 6 ∧ acceleratedOrbit 15 27963 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27963) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27963.1, data_15_27963.2]

/-- Complete interval computation for depth 15, residue 27964. -/
theorem bounds_15_27964 : exactInterval 15 27964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27964 : oddCount 27964 15 = 7 ∧ acceleratedOrbit 15 27964 = 1867 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27964) = 3 ^ 7 * m + 1867 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27964.1, data_15_27964.2]

/-- Complete interval computation for depth 15, residue 27965. -/
theorem bounds_15_27965 : exactInterval 15 27965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27965 : oddCount 27965 15 = 7 ∧ acceleratedOrbit 15 27965 = 1867 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27965) = 3 ^ 7 * m + 1867 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27965.1, data_15_27965.2]

/-- Complete interval computation for depth 15, residue 27966. -/
theorem bounds_15_27966 : exactInterval 15 27966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27966 : oddCount 27966 15 = 12 ∧ acceleratedOrbit 15 27966 = 453599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27966) = 3 ^ 12 * m + 453599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27966.1, data_15_27966.2]

/-- Complete interval computation for depth 15, residue 27967. -/
theorem bounds_15_27967 : exactInterval 15 27967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27967 : oddCount 27967 15 = 12 ∧ acceleratedOrbit 15 27967 = 453599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27967) = 3 ^ 12 * m + 453599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27967.1, data_15_27967.2]

/-- Complete interval computation for depth 15, residue 27968. -/
theorem bounds_15_27968 : exactInterval 15 27968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27968 : oddCount 27968 15 = 4 ∧ acceleratedOrbit 15 27968 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27968) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27968.1, data_15_27968.2]

/-- Complete interval computation for depth 15, residue 27969. -/
theorem bounds_15_27969 : exactInterval 15 27969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27969 : oddCount 27969 15 = 6 ∧ acceleratedOrbit 15 27969 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27969) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27969.1, data_15_27969.2]

/-- Complete interval computation for depth 15, residue 27970. -/
theorem bounds_15_27970 : exactInterval 15 27970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27970 : oddCount 27970 15 = 8 ∧ acceleratedOrbit 15 27970 = 5602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27970) = 3 ^ 8 * m + 5602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27970.1, data_15_27970.2]

/-- Complete interval computation for depth 15, residue 27971. -/
theorem bounds_15_27971 : exactInterval 15 27971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27971 : oddCount 27971 15 = 8 ∧ acceleratedOrbit 15 27971 = 5602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27971) = 3 ^ 8 * m + 5602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27971.1, data_15_27971.2]

/-- Complete interval computation for depth 15, residue 27972. -/
theorem bounds_15_27972 : exactInterval 15 27972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27972 : oddCount 27972 15 = 7 ∧ acceleratedOrbit 15 27972 = 1868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27972) = 3 ^ 7 * m + 1868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27972.1, data_15_27972.2]

/-- Complete interval computation for depth 15, residue 27973. -/
theorem bounds_15_27973 : exactInterval 15 27973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27973 : oddCount 27973 15 = 7 ∧ acceleratedOrbit 15 27973 = 1868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27973) = 3 ^ 7 * m + 1868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27973.1, data_15_27973.2]

/-- Complete interval computation for depth 15, residue 27974. -/
theorem bounds_15_27974 : exactInterval 15 27974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27974 : oddCount 27974 15 = 7 ∧ acceleratedOrbit 15 27974 = 1868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27974) = 3 ^ 7 * m + 1868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27974.1, data_15_27974.2]

/-- Complete interval computation for depth 15, residue 27975. -/
theorem bounds_15_27975 : exactInterval 15 27975 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27975) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27975 : oddCount 27975 15 = 9 ∧ acceleratedOrbit 15 27975 = 16805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27975) = 3 ^ 9 * m + 16805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27975.1, data_15_27975.2]

/-- Complete interval computation for depth 15, residue 27976. -/
theorem bounds_15_27976 : exactInterval 15 27976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27976 : oddCount 27976 15 = 7 ∧ acceleratedOrbit 15 27976 = 1868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27976) = 3 ^ 7 * m + 1868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27976.1, data_15_27976.2]

/-- Complete interval computation for depth 15, residue 27977. -/
theorem bounds_15_27977 : exactInterval 15 27977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27977 : oddCount 27977 15 = 10 ∧ acceleratedOrbit 15 27977 = 50422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27977) = 3 ^ 10 * m + 50422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27977.1, data_15_27977.2]

/-- Complete interval computation for depth 15, residue 27978. -/
theorem bounds_15_27978 : exactInterval 15 27978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27978 : oddCount 27978 15 = 7 ∧ acceleratedOrbit 15 27978 = 1868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27978) = 3 ^ 7 * m + 1868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27978.1, data_15_27978.2]

/-- Complete interval computation for depth 15, residue 27979. -/
theorem bounds_15_27979 : exactInterval 15 27979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27979 : oddCount 27979 15 = 7 ∧ acceleratedOrbit 15 27979 = 1868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27979) = 3 ^ 7 * m + 1868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27979.1, data_15_27979.2]

/-- Complete interval computation for depth 15, residue 27980. -/
theorem bounds_15_27980 : exactInterval 15 27980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27980 : oddCount 27980 15 = 7 ∧ acceleratedOrbit 15 27980 = 1868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27980) = 3 ^ 7 * m + 1868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27980.1, data_15_27980.2]

/-- Complete interval computation for depth 15, residue 27981. -/
theorem bounds_15_27981 : exactInterval 15 27981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27981 : oddCount 27981 15 = 7 ∧ acceleratedOrbit 15 27981 = 1868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27981) = 3 ^ 7 * m + 1868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27981.1, data_15_27981.2]

/-- Complete interval computation for depth 15, residue 27982. -/
theorem bounds_15_27982 : exactInterval 15 27982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27982 : oddCount 27982 15 = 9 ∧ acceleratedOrbit 15 27982 = 16811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27982) = 3 ^ 9 * m + 16811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27982.1, data_15_27982.2]

end Collatz.Research.PassageAtlas.Batch0854
