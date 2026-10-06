import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0732

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23953. -/
theorem bounds_15_23953 : exactInterval 15 23953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23953 : oddCount 23953 15 = 8 ∧ acceleratedOrbit 15 23953 = 4799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23953) = 3 ^ 8 * m + 4799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23953.1, data_15_23953.2]

/-- Complete interval computation for depth 15, residue 23954. -/
theorem bounds_15_23954 : exactInterval 15 23954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23954 : oddCount 23954 15 = 8 ∧ acceleratedOrbit 15 23954 = 4799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23954) = 3 ^ 8 * m + 4799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23954.1, data_15_23954.2]

/-- Complete interval computation for depth 15, residue 23955. -/
theorem bounds_15_23955 : exactInterval 15 23955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23955 : oddCount 23955 15 = 8 ∧ acceleratedOrbit 15 23955 = 4799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23955) = 3 ^ 8 * m + 4799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23955.1, data_15_23955.2]

/-- Complete interval computation for depth 15, residue 23956. -/
theorem bounds_15_23956 : exactInterval 15 23956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23956 : oddCount 23956 15 = 5 ∧ acceleratedOrbit 15 23956 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23956) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23956.1, data_15_23956.2]

/-- Complete interval computation for depth 15, residue 23957. -/
theorem bounds_15_23957 : exactInterval 15 23957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23957 : oddCount 23957 15 = 5 ∧ acceleratedOrbit 15 23957 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23957) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23957.1, data_15_23957.2]

/-- Complete interval computation for depth 15, residue 23958. -/
theorem bounds_15_23958 : exactInterval 15 23958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23958 : oddCount 23958 15 = 8 ∧ acceleratedOrbit 15 23958 = 4799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23958) = 3 ^ 8 * m + 4799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23958.1, data_15_23958.2]

/-- Complete interval computation for depth 15, residue 23959. -/
theorem bounds_15_23959 : exactInterval 15 23959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23959 : oddCount 23959 15 = 8 ∧ acceleratedOrbit 15 23959 = 4799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23959) = 3 ^ 8 * m + 4799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23959.1, data_15_23959.2]

/-- Complete interval computation for depth 15, residue 23960. -/
theorem bounds_15_23960 : exactInterval 15 23960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23960 : oddCount 23960 15 = 5 ∧ acceleratedOrbit 15 23960 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23960) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23960.1, data_15_23960.2]

/-- Complete interval computation for depth 15, residue 23961. -/
theorem bounds_15_23961 : exactInterval 15 23961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23961 : oddCount 23961 15 = 8 ∧ acceleratedOrbit 15 23961 = 4799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23961) = 3 ^ 8 * m + 4799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23961.1, data_15_23961.2]

/-- Complete interval computation for depth 15, residue 23962. -/
theorem bounds_15_23962 : exactInterval 15 23962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23962 : oddCount 23962 15 = 5 ∧ acceleratedOrbit 15 23962 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23962) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23962.1, data_15_23962.2]

/-- Complete interval computation for depth 15, residue 23963. -/
theorem bounds_15_23963 : exactInterval 15 23963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23963 : oddCount 23963 15 = 10 ∧ acceleratedOrbit 15 23963 = 43186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23963) = 3 ^ 10 * m + 43186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23963.1, data_15_23963.2]

/-- Complete interval computation for depth 15, residue 23964. -/
theorem bounds_15_23964 : exactInterval 15 23964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23964 : oddCount 23964 15 = 10 ∧ acceleratedOrbit 15 23964 = 43193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23964) = 3 ^ 10 * m + 43193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23964.1, data_15_23964.2]

/-- Complete interval computation for depth 15, residue 23965. -/
theorem bounds_15_23965 : exactInterval 15 23965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23965 : oddCount 23965 15 = 10 ∧ acceleratedOrbit 15 23965 = 43193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23965) = 3 ^ 10 * m + 43193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23965.1, data_15_23965.2]

/-- Complete interval computation for depth 15, residue 23966. -/
theorem bounds_15_23966 : exactInterval 15 23966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23966 : oddCount 23966 15 = 10 ∧ acceleratedOrbit 15 23966 = 43193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23966) = 3 ^ 10 * m + 43193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23966.1, data_15_23966.2]

/-- Complete interval computation for depth 15, residue 23967. -/
theorem bounds_15_23967 : exactInterval 15 23967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23967 : oddCount 23967 15 = 11 ∧ acceleratedOrbit 15 23967 = 129575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23967) = 3 ^ 11 * m + 129575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23967.1, data_15_23967.2]

/-- Complete interval computation for depth 15, residue 23968. -/
theorem bounds_15_23968 : exactInterval 15 23968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23968 : oddCount 23968 15 = 5 ∧ acceleratedOrbit 15 23968 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23968) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23968.1, data_15_23968.2]

/-- Complete interval computation for depth 15, residue 23969. -/
theorem bounds_15_23969 : exactInterval 15 23969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23969 : oddCount 23969 15 = 7 ∧ acceleratedOrbit 15 23969 = 1600 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23969) = 3 ^ 7 * m + 1600 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23969.1, data_15_23969.2]

/-- Complete interval computation for depth 15, residue 23970. -/
theorem bounds_15_23970 : exactInterval 15 23970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23970 : oddCount 23970 15 = 7 ∧ acceleratedOrbit 15 23970 = 1601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23970) = 3 ^ 7 * m + 1601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23970.1, data_15_23970.2]

/-- Complete interval computation for depth 15, residue 23971. -/
theorem bounds_15_23971 : exactInterval 15 23971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23971 : oddCount 23971 15 = 7 ∧ acceleratedOrbit 15 23971 = 1601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23971) = 3 ^ 7 * m + 1601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23971.1, data_15_23971.2]

/-- Complete interval computation for depth 15, residue 23972. -/
theorem bounds_15_23972 : exactInterval 15 23972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23972 : oddCount 23972 15 = 7 ∧ acceleratedOrbit 15 23972 = 1601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23972) = 3 ^ 7 * m + 1601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23972.1, data_15_23972.2]

/-- Complete interval computation for depth 15, residue 23973. -/
theorem bounds_15_23973 : exactInterval 15 23973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23973 : oddCount 23973 15 = 7 ∧ acceleratedOrbit 15 23973 = 1601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23973) = 3 ^ 7 * m + 1601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23973.1, data_15_23973.2]

/-- Complete interval computation for depth 15, residue 23974. -/
theorem bounds_15_23974 : exactInterval 15 23974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23974 : oddCount 23974 15 = 7 ∧ acceleratedOrbit 15 23974 = 1601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23974) = 3 ^ 7 * m + 1601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23974.1, data_15_23974.2]

/-- Complete interval computation for depth 15, residue 23975. -/
theorem bounds_15_23975 : exactInterval 15 23975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23975 : oddCount 23975 15 = 8 ∧ acceleratedOrbit 15 23975 = 4801 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23975) = 3 ^ 8 * m + 4801 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23975.1, data_15_23975.2]

/-- Complete interval computation for depth 15, residue 23976. -/
theorem bounds_15_23976 : exactInterval 15 23976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23976 : oddCount 23976 15 = 5 ∧ acceleratedOrbit 15 23976 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23976) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23976.1, data_15_23976.2]

/-- Complete interval computation for depth 15, residue 23977. -/
theorem bounds_15_23977 : exactInterval 15 23977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23977 : oddCount 23977 15 = 9 ∧ acceleratedOrbit 15 23977 = 14404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23977) = 3 ^ 9 * m + 14404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23977.1, data_15_23977.2]

/-- Complete interval computation for depth 15, residue 23978. -/
theorem bounds_15_23978 : exactInterval 15 23978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23978 : oddCount 23978 15 = 5 ∧ acceleratedOrbit 15 23978 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23978) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23978.1, data_15_23978.2]

/-- Complete interval computation for depth 15, residue 23979. -/
theorem bounds_15_23979 : exactInterval 15 23979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23979 : oddCount 23979 15 = 10 ∧ acceleratedOrbit 15 23979 = 43217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23979) = 3 ^ 10 * m + 43217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23979.1, data_15_23979.2]

/-- Complete interval computation for depth 15, residue 23980. -/
theorem bounds_15_23980 : exactInterval 15 23980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23980 : oddCount 23980 15 = 8 ∧ acceleratedOrbit 15 23980 = 4805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23980) = 3 ^ 8 * m + 4805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23980.1, data_15_23980.2]

/-- Complete interval computation for depth 15, residue 23981. -/
theorem bounds_15_23981 : exactInterval 15 23981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23981 : oddCount 23981 15 = 8 ∧ acceleratedOrbit 15 23981 = 4805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23981) = 3 ^ 8 * m + 4805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23981.1, data_15_23981.2]

/-- Complete interval computation for depth 15, residue 23982. -/
theorem bounds_15_23982 : exactInterval 15 23982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23982 : oddCount 23982 15 = 8 ∧ acceleratedOrbit 15 23982 = 4805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23982) = 3 ^ 8 * m + 4805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23982.1, data_15_23982.2]

/-- Complete interval computation for depth 15, residue 23983. -/
theorem bounds_15_23983 : exactInterval 15 23983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23983 : oddCount 23983 15 = 9 ∧ acceleratedOrbit 15 23983 = 14408 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23983) = 3 ^ 9 * m + 14408 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23983.1, data_15_23983.2]

/-- Complete interval computation for depth 15, residue 23984. -/
theorem bounds_15_23984 : exactInterval 15 23984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23984 : oddCount 23984 15 = 5 ∧ acceleratedOrbit 15 23984 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23984) = 3 ^ 5 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23984.1, data_15_23984.2]

/-- Complete interval computation for depth 15, residue 23985. -/
theorem bounds_15_23985 : exactInterval 15 23985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23985 : oddCount 23985 15 = 5 ∧ acceleratedOrbit 15 23985 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23985) = 3 ^ 5 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23985.1, data_15_23985.2]

end Collatz.Research.PassageAtlas.Batch0732
