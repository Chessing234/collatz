import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0671

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21954. -/
theorem bounds_15_21954 : exactInterval 15 21954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21954 : oddCount 21954 15 = 10 ∧ acceleratedOrbit 15 21954 = 39572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21954) = 3 ^ 10 * m + 39572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21954.1, data_15_21954.2]

/-- Complete interval computation for depth 15, residue 21955. -/
theorem bounds_15_21955 : exactInterval 15 21955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21955 : oddCount 21955 15 = 10 ∧ acceleratedOrbit 15 21955 = 39572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21955) = 3 ^ 10 * m + 39572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21955.1, data_15_21955.2]

/-- Complete interval computation for depth 15, residue 21956. -/
theorem bounds_15_21956 : exactInterval 15 21956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21956 : oddCount 21956 15 = 5 ∧ acceleratedOrbit 15 21956 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21956) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21956.1, data_15_21956.2]

/-- Complete interval computation for depth 15, residue 21957. -/
theorem bounds_15_21957 : exactInterval 15 21957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21957 : oddCount 21957 15 = 5 ∧ acceleratedOrbit 15 21957 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21957) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21957.1, data_15_21957.2]

/-- Complete interval computation for depth 15, residue 21958. -/
theorem bounds_15_21958 : exactInterval 15 21958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21958 : oddCount 21958 15 = 5 ∧ acceleratedOrbit 15 21958 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21958) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21958.1, data_15_21958.2]

/-- Complete interval computation for depth 15, residue 21959. -/
theorem bounds_15_21959 : exactInterval 15 21959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21959 : oddCount 21959 15 = 9 ∧ acceleratedOrbit 15 21959 = 13193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21959) = 3 ^ 9 * m + 13193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21959.1, data_15_21959.2]

/-- Complete interval computation for depth 15, residue 21960. -/
theorem bounds_15_21960 : exactInterval 15 21960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21960 : oddCount 21960 15 = 5 ∧ acceleratedOrbit 15 21960 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21960) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21960.1, data_15_21960.2]

/-- Complete interval computation for depth 15, residue 21961. -/
theorem bounds_15_21961 : exactInterval 15 21961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21961 : oddCount 21961 15 = 8 ∧ acceleratedOrbit 15 21961 = 4400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21961) = 3 ^ 8 * m + 4400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21961.1, data_15_21961.2]

/-- Complete interval computation for depth 15, residue 21962. -/
theorem bounds_15_21962 : exactInterval 15 21962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21962 : oddCount 21962 15 = 5 ∧ acceleratedOrbit 15 21962 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21962) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21962.1, data_15_21962.2]

/-- Complete interval computation for depth 15, residue 21963. -/
theorem bounds_15_21963 : exactInterval 15 21963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21963 : oddCount 21963 15 = 8 ∧ acceleratedOrbit 15 21963 = 4400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21963) = 3 ^ 8 * m + 4400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21963.1, data_15_21963.2]

/-- Complete interval computation for depth 15, residue 21964. -/
theorem bounds_15_21964 : exactInterval 15 21964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21964 : oddCount 21964 15 = 5 ∧ acceleratedOrbit 15 21964 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21964) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21964.1, data_15_21964.2]

/-- Complete interval computation for depth 15, residue 21965. -/
theorem bounds_15_21965 : exactInterval 15 21965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21965 : oddCount 21965 15 = 5 ∧ acceleratedOrbit 15 21965 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21965) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21965.1, data_15_21965.2]

/-- Complete interval computation for depth 15, residue 21966. -/
theorem bounds_15_21966 : exactInterval 15 21966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21966 : oddCount 21966 15 = 11 ∧ acceleratedOrbit 15 21966 = 118766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21966) = 3 ^ 11 * m + 118766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21966.1, data_15_21966.2]

/-- Complete interval computation for depth 15, residue 21967. -/
theorem bounds_15_21967 : exactInterval 15 21967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21967 : oddCount 21967 15 = 11 ∧ acceleratedOrbit 15 21967 = 118766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21967) = 3 ^ 11 * m + 118766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21967.1, data_15_21967.2]

/-- Complete interval computation for depth 15, residue 21968. -/
theorem bounds_15_21968 : exactInterval 15 21968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21968 : oddCount 21968 15 = 5 ∧ acceleratedOrbit 15 21968 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21968) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21968.1, data_15_21968.2]

/-- Complete interval computation for depth 15, residue 21969. -/
theorem bounds_15_21969 : exactInterval 15 21969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21969 : oddCount 21969 15 = 5 ∧ acceleratedOrbit 15 21969 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21969) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21969.1, data_15_21969.2]

/-- Complete interval computation for depth 15, residue 21970. -/
theorem bounds_15_21970 : exactInterval 15 21970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21970 : oddCount 21970 15 = 10 ∧ acceleratedOrbit 15 21970 = 39599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21970) = 3 ^ 10 * m + 39599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21970.1, data_15_21970.2]

/-- Complete interval computation for depth 15, residue 21971. -/
theorem bounds_15_21971 : exactInterval 15 21971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21971 : oddCount 21971 15 = 10 ∧ acceleratedOrbit 15 21971 = 39599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21971) = 3 ^ 10 * m + 39599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21971.1, data_15_21971.2]

/-- Complete interval computation for depth 15, residue 21972. -/
theorem bounds_15_21972 : exactInterval 15 21972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21972 : oddCount 21972 15 = 5 ∧ acceleratedOrbit 15 21972 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21972) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21972.1, data_15_21972.2]

/-- Complete interval computation for depth 15, residue 21973. -/
theorem bounds_15_21973 : exactInterval 15 21973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21973 : oddCount 21973 15 = 5 ∧ acceleratedOrbit 15 21973 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21973) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21973.1, data_15_21973.2]

/-- Complete interval computation for depth 15, residue 21974. -/
theorem bounds_15_21974 : exactInterval 15 21974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21974 : oddCount 21974 15 = 10 ∧ acceleratedOrbit 15 21974 = 39608 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21974) = 3 ^ 10 * m + 39608 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21974.1, data_15_21974.2]

/-- Complete interval computation for depth 15, residue 21975. -/
theorem bounds_15_21975 : exactInterval 15 21975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21975 : oddCount 21975 15 = 10 ∧ acceleratedOrbit 15 21975 = 39608 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21975) = 3 ^ 10 * m + 39608 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21975.1, data_15_21975.2]

/-- Complete interval computation for depth 15, residue 21976. -/
theorem bounds_15_21976 : exactInterval 15 21976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21976 : oddCount 21976 15 = 7 ∧ acceleratedOrbit 15 21976 = 1468 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21976) = 3 ^ 7 * m + 1468 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21976.1, data_15_21976.2]

/-- Complete interval computation for depth 15, residue 21977. -/
theorem bounds_15_21977 : exactInterval 15 21977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21977 : oddCount 21977 15 = 7 ∧ acceleratedOrbit 15 21977 = 1468 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21977) = 3 ^ 7 * m + 1468 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21977.1, data_15_21977.2]

/-- Complete interval computation for depth 15, residue 21978. -/
theorem bounds_15_21978 : exactInterval 15 21978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21978 : oddCount 21978 15 = 7 ∧ acceleratedOrbit 15 21978 = 1468 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21978) = 3 ^ 7 * m + 1468 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21978.1, data_15_21978.2]

/-- Complete interval computation for depth 15, residue 21979. -/
theorem bounds_15_21979 : exactInterval 15 21979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21979 : oddCount 21979 15 = 5 ∧ acceleratedOrbit 15 21979 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21979) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21979.1, data_15_21979.2]

/-- Complete interval computation for depth 15, residue 21980. -/
theorem bounds_15_21980 : exactInterval 15 21980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21980 : oddCount 21980 15 = 7 ∧ acceleratedOrbit 15 21980 = 1468 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21980) = 3 ^ 7 * m + 1468 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21980.1, data_15_21980.2]

/-- Complete interval computation for depth 15, residue 21981. -/
theorem bounds_15_21981 : exactInterval 15 21981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21981 : oddCount 21981 15 = 7 ∧ acceleratedOrbit 15 21981 = 1468 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21981) = 3 ^ 7 * m + 1468 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21981.1, data_15_21981.2]

/-- Complete interval computation for depth 15, residue 21982. -/
theorem bounds_15_21982 : exactInterval 15 21982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21982 : oddCount 21982 15 = 10 ∧ acceleratedOrbit 15 21982 = 39617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21982) = 3 ^ 10 * m + 39617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21982.1, data_15_21982.2]

/-- Complete interval computation for depth 15, residue 21983. -/
theorem bounds_15_21983 : exactInterval 15 21983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21983 : oddCount 21983 15 = 10 ∧ acceleratedOrbit 15 21983 = 39617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21983) = 3 ^ 10 * m + 39617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21983.1, data_15_21983.2]

/-- Complete interval computation for depth 15, residue 21984. -/
theorem bounds_15_21984 : exactInterval 15 21984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21984 : oddCount 21984 15 = 6 ∧ acceleratedOrbit 15 21984 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21984) = 3 ^ 6 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21984.1, data_15_21984.2]

/-- Complete interval computation for depth 15, residue 21985. -/
theorem bounds_15_21985 : exactInterval 15 21985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21985 : oddCount 21985 15 = 8 ∧ acceleratedOrbit 15 21985 = 4403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21985) = 3 ^ 8 * m + 4403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21985.1, data_15_21985.2]

/-- Complete interval computation for depth 15, residue 21986. -/
theorem bounds_15_21986 : exactInterval 15 21986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21986 : oddCount 21986 15 = 5 ∧ acceleratedOrbit 15 21986 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21986) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21986.1, data_15_21986.2]

end Collatz.Research.PassageAtlas.Batch0671
