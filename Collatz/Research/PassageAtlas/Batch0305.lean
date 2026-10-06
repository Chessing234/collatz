import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0305

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9961. -/
theorem bounds_15_9961 : exactInterval 15 9961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9961 : oddCount 9961 15 = 11 ∧ acceleratedOrbit 15 9961 = 53864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9961) = 3 ^ 11 * m + 53864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9961.1, data_15_9961.2]

/-- Complete interval computation for depth 15, residue 9962. -/
theorem bounds_15_9962 : exactInterval 15 9962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9962 : oddCount 9962 15 = 7 ∧ acceleratedOrbit 15 9962 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9962) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9962.1, data_15_9962.2]

/-- Complete interval computation for depth 15, residue 9963. -/
theorem bounds_15_9963 : exactInterval 15 9963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9963 : oddCount 9963 15 = 9 ∧ acceleratedOrbit 15 9963 = 5987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9963) = 3 ^ 9 * m + 5987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9963.1, data_15_9963.2]

/-- Complete interval computation for depth 15, residue 9964. -/
theorem bounds_15_9964 : exactInterval 15 9964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9964 : oddCount 9964 15 = 9 ∧ acceleratedOrbit 15 9964 = 5993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9964) = 3 ^ 9 * m + 5993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9964.1, data_15_9964.2]

/-- Complete interval computation for depth 15, residue 9965. -/
theorem bounds_15_9965 : exactInterval 15 9965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9965 : oddCount 9965 15 = 9 ∧ acceleratedOrbit 15 9965 = 5993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9965) = 3 ^ 9 * m + 5993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9965.1, data_15_9965.2]

/-- Complete interval computation for depth 15, residue 9966. -/
theorem bounds_15_9966 : exactInterval 15 9966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9966 : oddCount 9966 15 = 9 ∧ acceleratedOrbit 15 9966 = 5993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9966) = 3 ^ 9 * m + 5993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9966.1, data_15_9966.2]

/-- Complete interval computation for depth 15, residue 9967. -/
theorem bounds_15_9967 : exactInterval 15 9967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9967 : oddCount 9967 15 = 11 ∧ acceleratedOrbit 15 9967 = 53891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9967) = 3 ^ 11 * m + 53891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9967.1, data_15_9967.2]

/-- Complete interval computation for depth 15, residue 9968. -/
theorem bounds_15_9968 : exactInterval 15 9968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9968 : oddCount 9968 15 = 8 ∧ acceleratedOrbit 15 9968 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9968) = 3 ^ 8 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9968.1, data_15_9968.2]

/-- Complete interval computation for depth 15, residue 9969. -/
theorem bounds_15_9969 : exactInterval 15 9969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9969 : oddCount 9969 15 = 7 ∧ acceleratedOrbit 15 9969 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9969) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9969.1, data_15_9969.2]

/-- Complete interval computation for depth 15, residue 9970. -/
theorem bounds_15_9970 : exactInterval 15 9970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9970 : oddCount 9970 15 = 10 ∧ acceleratedOrbit 15 9970 = 17975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9970) = 3 ^ 10 * m + 17975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9970.1, data_15_9970.2]

/-- Complete interval computation for depth 15, residue 9971. -/
theorem bounds_15_9971 : exactInterval 15 9971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9971 : oddCount 9971 15 = 10 ∧ acceleratedOrbit 15 9971 = 17975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9971) = 3 ^ 10 * m + 17975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9971.1, data_15_9971.2]

/-- Complete interval computation for depth 15, residue 9972. -/
theorem bounds_15_9972 : exactInterval 15 9972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9972 : oddCount 9972 15 = 8 ∧ acceleratedOrbit 15 9972 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9972) = 3 ^ 8 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9972.1, data_15_9972.2]

/-- Complete interval computation for depth 15, residue 9973. -/
theorem bounds_15_9973 : exactInterval 15 9973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9973 : oddCount 9973 15 = 8 ∧ acceleratedOrbit 15 9973 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9973) = 3 ^ 8 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9973.1, data_15_9973.2]

/-- Complete interval computation for depth 15, residue 9974. -/
theorem bounds_15_9974 : exactInterval 15 9974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9974 : oddCount 9974 15 = 11 ∧ acceleratedOrbit 15 9974 = 53945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9974) = 3 ^ 11 * m + 53945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9974.1, data_15_9974.2]

/-- Complete interval computation for depth 15, residue 9975. -/
theorem bounds_15_9975 : exactInterval 15 9975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9975 : oddCount 9975 15 = 11 ∧ acceleratedOrbit 15 9975 = 53945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9975) = 3 ^ 11 * m + 53945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9975.1, data_15_9975.2]

/-- Complete interval computation for depth 15, residue 9976. -/
theorem bounds_15_9976 : exactInterval 15 9976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9976 : oddCount 9976 15 = 8 ∧ acceleratedOrbit 15 9976 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9976) = 3 ^ 8 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9976.1, data_15_9976.2]

/-- Complete interval computation for depth 15, residue 9977. -/
theorem bounds_15_9977 : exactInterval 15 9977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9977 : oddCount 9977 15 = 5 ∧ acceleratedOrbit 15 9977 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9977) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9977.1, data_15_9977.2]

/-- Complete interval computation for depth 15, residue 9978. -/
theorem bounds_15_9978 : exactInterval 15 9978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9978 : oddCount 9978 15 = 8 ∧ acceleratedOrbit 15 9978 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9978) = 3 ^ 8 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9978.1, data_15_9978.2]

/-- Complete interval computation for depth 15, residue 9979. -/
theorem bounds_15_9979 : exactInterval 15 9979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9979 : oddCount 9979 15 = 9 ∧ acceleratedOrbit 15 9979 = 5996 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9979) = 3 ^ 9 * m + 5996 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9979.1, data_15_9979.2]

/-- Complete interval computation for depth 15, residue 9980. -/
theorem bounds_15_9980 : exactInterval 15 9980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9980 : oddCount 9980 15 = 10 ∧ acceleratedOrbit 15 9980 = 17992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9980) = 3 ^ 10 * m + 17992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9980.1, data_15_9980.2]

/-- Complete interval computation for depth 15, residue 9981. -/
theorem bounds_15_9981 : exactInterval 15 9981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9981 : oddCount 9981 15 = 10 ∧ acceleratedOrbit 15 9981 = 17992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9981) = 3 ^ 10 * m + 17992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9981.1, data_15_9981.2]

/-- Complete interval computation for depth 15, residue 9982. -/
theorem bounds_15_9982 : exactInterval 15 9982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9982 : oddCount 9982 15 = 10 ∧ acceleratedOrbit 15 9982 = 17992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9982) = 3 ^ 10 * m + 17992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9982.1, data_15_9982.2]

/-- Complete interval computation for depth 15, residue 9983. -/
theorem bounds_15_9983 : exactInterval 15 9983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9983 : oddCount 9983 15 = 11 ∧ acceleratedOrbit 15 9983 = 53975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9983) = 3 ^ 11 * m + 53975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9983.1, data_15_9983.2]

/-- Complete interval computation for depth 15, residue 9984. -/
theorem bounds_15_9984 : exactInterval 15 9984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9984 : oddCount 9984 15 = 5 ∧ acceleratedOrbit 15 9984 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9984) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9984.1, data_15_9984.2]

/-- Complete interval computation for depth 15, residue 9985. -/
theorem bounds_15_9985 : exactInterval 15 9985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9985 : oddCount 9985 15 = 7 ∧ acceleratedOrbit 15 9985 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9985) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9985.1, data_15_9985.2]

/-- Complete interval computation for depth 15, residue 9986. -/
theorem bounds_15_9986 : exactInterval 15 9986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9986 : oddCount 9986 15 = 7 ∧ acceleratedOrbit 15 9986 = 667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9986) = 3 ^ 7 * m + 667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9986.1, data_15_9986.2]

/-- Complete interval computation for depth 15, residue 9987. -/
theorem bounds_15_9987 : exactInterval 15 9987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9987 : oddCount 9987 15 = 7 ∧ acceleratedOrbit 15 9987 = 667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9987) = 3 ^ 7 * m + 667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9987.1, data_15_9987.2]

/-- Complete interval computation for depth 15, residue 9988. -/
theorem bounds_15_9988 : exactInterval 15 9988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9988 : oddCount 9988 15 = 7 ∧ acceleratedOrbit 15 9988 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9988) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9988.1, data_15_9988.2]

/-- Complete interval computation for depth 15, residue 9989. -/
theorem bounds_15_9989 : exactInterval 15 9989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9989 : oddCount 9989 15 = 7 ∧ acceleratedOrbit 15 9989 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9989) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9989.1, data_15_9989.2]

/-- Complete interval computation for depth 15, residue 9990. -/
theorem bounds_15_9990 : exactInterval 15 9990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9990 : oddCount 9990 15 = 7 ∧ acceleratedOrbit 15 9990 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9990) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9990.1, data_15_9990.2]

/-- Complete interval computation for depth 15, residue 9991. -/
theorem bounds_15_9991 : exactInterval 15 9991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9991 : oddCount 9991 15 = 7 ∧ acceleratedOrbit 15 9991 = 667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9991) = 3 ^ 7 * m + 667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9991.1, data_15_9991.2]

/-- Complete interval computation for depth 15, residue 9992. -/
theorem bounds_15_9992 : exactInterval 15 9992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9992 : oddCount 9992 15 = 9 ∧ acceleratedOrbit 15 9992 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9992) = 3 ^ 9 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9992.1, data_15_9992.2]

/-- Complete interval computation for depth 15, residue 9993. -/
theorem bounds_15_9993 : exactInterval 15 9993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9993 : oddCount 9993 15 = 9 ∧ acceleratedOrbit 15 9993 = 6004 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9993) = 3 ^ 9 * m + 6004 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9993.1, data_15_9993.2]

end Collatz.Research.PassageAtlas.Batch0305
