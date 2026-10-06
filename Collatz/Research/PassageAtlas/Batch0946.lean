import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0946

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30965. -/
theorem bounds_15_30965 : exactInterval 15 30965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30965 : oddCount 30965 15 = 7 ∧ acceleratedOrbit 15 30965 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30965) = 3 ^ 7 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30965.1, data_15_30965.2]

/-- Complete interval computation for depth 15, residue 30966. -/
theorem bounds_15_30966 : exactInterval 15 30966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30966 : oddCount 30966 15 = 6 ∧ acceleratedOrbit 15 30966 = 689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30966) = 3 ^ 6 * m + 689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30966.1, data_15_30966.2]

/-- Complete interval computation for depth 15, residue 30967. -/
theorem bounds_15_30967 : exactInterval 15 30967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30967 : oddCount 30967 15 = 6 ∧ acceleratedOrbit 15 30967 = 689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30967) = 3 ^ 6 * m + 689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30967.1, data_15_30967.2]

/-- Complete interval computation for depth 15, residue 30968. -/
theorem bounds_15_30968 : exactInterval 15 30968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30968 : oddCount 30968 15 = 8 ∧ acceleratedOrbit 15 30968 = 6203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30968) = 3 ^ 8 * m + 6203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30968.1, data_15_30968.2]

/-- Complete interval computation for depth 15, residue 30969. -/
theorem bounds_15_30969 : exactInterval 15 30969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30969 : oddCount 30969 15 = 9 ∧ acceleratedOrbit 15 30969 = 18605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30969) = 3 ^ 9 * m + 18605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30969.1, data_15_30969.2]

/-- Complete interval computation for depth 15, residue 30970. -/
theorem bounds_15_30970 : exactInterval 15 30970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30970 : oddCount 30970 15 = 8 ∧ acceleratedOrbit 15 30970 = 6203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30970) = 3 ^ 8 * m + 6203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30970.1, data_15_30970.2]

/-- Complete interval computation for depth 15, residue 30971. -/
theorem bounds_15_30971 : exactInterval 15 30971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30971 : oddCount 30971 15 = 10 ∧ acceleratedOrbit 15 30971 = 55814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30971) = 3 ^ 10 * m + 55814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30971.1, data_15_30971.2]

/-- Complete interval computation for depth 15, residue 30972. -/
theorem bounds_15_30972 : exactInterval 15 30972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30972 : oddCount 30972 15 = 8 ∧ acceleratedOrbit 15 30972 = 6203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30972) = 3 ^ 8 * m + 6203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30972.1, data_15_30972.2]

/-- Complete interval computation for depth 15, residue 30973. -/
theorem bounds_15_30973 : exactInterval 15 30973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30973 : oddCount 30973 15 = 8 ∧ acceleratedOrbit 15 30973 = 6203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30973) = 3 ^ 8 * m + 6203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30973.1, data_15_30973.2]

/-- Complete interval computation for depth 15, residue 30974. -/
theorem bounds_15_30974 : exactInterval 15 30974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30974 : oddCount 30974 15 = 10 ∧ acceleratedOrbit 15 30974 = 55820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30974) = 3 ^ 10 * m + 55820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30974.1, data_15_30974.2]

/-- Complete interval computation for depth 15, residue 30975. -/
theorem bounds_15_30975 : exactInterval 15 30975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30975 : oddCount 30975 15 = 10 ∧ acceleratedOrbit 15 30975 = 55820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30975) = 3 ^ 10 * m + 55820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30975.1, data_15_30975.2]

/-- Complete interval computation for depth 15, residue 30976. -/
theorem bounds_15_30976 : exactInterval 15 30976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30976 : oddCount 30976 15 = 5 ∧ acceleratedOrbit 15 30976 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30976) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30976.1, data_15_30976.2]

/-- Complete interval computation for depth 15, residue 30977. -/
theorem bounds_15_30977 : exactInterval 15 30977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30977 : oddCount 30977 15 = 7 ∧ acceleratedOrbit 15 30977 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30977) = 3 ^ 7 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30977.1, data_15_30977.2]

/-- Complete interval computation for depth 15, residue 30978. -/
theorem bounds_15_30978 : exactInterval 15 30978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30978 : oddCount 30978 15 = 7 ∧ acceleratedOrbit 15 30978 = 2068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30978) = 3 ^ 7 * m + 2068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30978.1, data_15_30978.2]

/-- Complete interval computation for depth 15, residue 30979. -/
theorem bounds_15_30979 : exactInterval 15 30979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30979 : oddCount 30979 15 = 7 ∧ acceleratedOrbit 15 30979 = 2068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30979) = 3 ^ 7 * m + 2068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30979.1, data_15_30979.2]

/-- Complete interval computation for depth 15, residue 30980. -/
theorem bounds_15_30980 : exactInterval 15 30980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30980 : oddCount 30980 15 = 5 ∧ acceleratedOrbit 15 30980 = 230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30980) = 3 ^ 5 * m + 230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30980.1, data_15_30980.2]

/-- Complete interval computation for depth 15, residue 30981. -/
theorem bounds_15_30981 : exactInterval 15 30981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30981 : oddCount 30981 15 = 5 ∧ acceleratedOrbit 15 30981 = 230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30981) = 3 ^ 5 * m + 230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30981.1, data_15_30981.2]

/-- Complete interval computation for depth 15, residue 30982. -/
theorem bounds_15_30982 : exactInterval 15 30982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30982 : oddCount 30982 15 = 5 ∧ acceleratedOrbit 15 30982 = 230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30982) = 3 ^ 5 * m + 230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30982.1, data_15_30982.2]

/-- Complete interval computation for depth 15, residue 30983. -/
theorem bounds_15_30983 : exactInterval 15 30983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30983 : oddCount 30983 15 = 7 ∧ acceleratedOrbit 15 30983 = 2068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30983) = 3 ^ 7 * m + 2068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30983.1, data_15_30983.2]

/-- Complete interval computation for depth 15, residue 30984. -/
theorem bounds_15_30984 : exactInterval 15 30984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30984 : oddCount 30984 15 = 5 ∧ acceleratedOrbit 15 30984 = 230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30984) = 3 ^ 5 * m + 230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30984.1, data_15_30984.2]

/-- Complete interval computation for depth 15, residue 30985. -/
theorem bounds_15_30985 : exactInterval 15 30985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30985 : oddCount 30985 15 = 8 ∧ acceleratedOrbit 15 30985 = 6205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30985) = 3 ^ 8 * m + 6205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30985.1, data_15_30985.2]

/-- Complete interval computation for depth 15, residue 30986. -/
theorem bounds_15_30986 : exactInterval 15 30986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30986 : oddCount 30986 15 = 5 ∧ acceleratedOrbit 15 30986 = 230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30986) = 3 ^ 5 * m + 230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30986.1, data_15_30986.2]

/-- Complete interval computation for depth 15, residue 30987. -/
theorem bounds_15_30987 : exactInterval 15 30987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30987 : oddCount 30987 15 = 7 ∧ acceleratedOrbit 15 30987 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30987) = 3 ^ 7 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30987.1, data_15_30987.2]

/-- Complete interval computation for depth 15, residue 30988. -/
theorem bounds_15_30988 : exactInterval 15 30988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30988 : oddCount 30988 15 = 5 ∧ acceleratedOrbit 15 30988 = 230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30988) = 3 ^ 5 * m + 230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30988.1, data_15_30988.2]

/-- Complete interval computation for depth 15, residue 30989. -/
theorem bounds_15_30989 : exactInterval 15 30989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30989 : oddCount 30989 15 = 5 ∧ acceleratedOrbit 15 30989 = 230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30989) = 3 ^ 5 * m + 230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30989.1, data_15_30989.2]

/-- Complete interval computation for depth 15, residue 30990. -/
theorem bounds_15_30990 : exactInterval 15 30990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30990 : oddCount 30990 15 = 9 ∧ acceleratedOrbit 15 30990 = 18620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30990) = 3 ^ 9 * m + 18620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30990.1, data_15_30990.2]

/-- Complete interval computation for depth 15, residue 30991. -/
theorem bounds_15_30991 : exactInterval 15 30991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30991 : oddCount 30991 15 = 9 ∧ acceleratedOrbit 15 30991 = 18620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30991) = 3 ^ 9 * m + 18620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30991.1, data_15_30991.2]

/-- Complete interval computation for depth 15, residue 30992. -/
theorem bounds_15_30992 : exactInterval 15 30992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30992 : oddCount 30992 15 = 6 ∧ acceleratedOrbit 15 30992 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30992) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30992.1, data_15_30992.2]

/-- Complete interval computation for depth 15, residue 30993. -/
theorem bounds_15_30993 : exactInterval 15 30993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30993 : oddCount 30993 15 = 5 ∧ acceleratedOrbit 15 30993 = 230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30993) = 3 ^ 5 * m + 230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30993.1, data_15_30993.2]

/-- Complete interval computation for depth 15, residue 30994. -/
theorem bounds_15_30994 : exactInterval 15 30994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30994 : oddCount 30994 15 = 11 ∧ acceleratedOrbit 15 30994 = 167579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30994) = 3 ^ 11 * m + 167579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30994.1, data_15_30994.2]

/-- Complete interval computation for depth 15, residue 30995. -/
theorem bounds_15_30995 : exactInterval 15 30995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30995 : oddCount 30995 15 = 11 ∧ acceleratedOrbit 15 30995 = 167579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30995) = 3 ^ 11 * m + 167579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30995.1, data_15_30995.2]

/-- Complete interval computation for depth 15, residue 30996. -/
theorem bounds_15_30996 : exactInterval 15 30996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30996 : oddCount 30996 15 = 6 ∧ acceleratedOrbit 15 30996 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30996) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30996.1, data_15_30996.2]

/-- Complete interval computation for depth 15, residue 30997. -/
theorem bounds_15_30997 : exactInterval 15 30997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30997 : oddCount 30997 15 = 6 ∧ acceleratedOrbit 15 30997 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30997) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30997.1, data_15_30997.2]

end Collatz.Research.PassageAtlas.Batch0946
