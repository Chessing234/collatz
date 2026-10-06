import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0427

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13959. -/
theorem bounds_15_13959 : exactInterval 15 13959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13959 : oddCount 13959 15 = 7 ∧ acceleratedOrbit 15 13959 = 932 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13959) = 3 ^ 7 * m + 932 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13959.1, data_15_13959.2]

/-- Complete interval computation for depth 15, residue 13960. -/
theorem bounds_15_13960 : exactInterval 15 13960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13960 : oddCount 13960 15 = 7 ∧ acceleratedOrbit 15 13960 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13960) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13960.1, data_15_13960.2]

/-- Complete interval computation for depth 15, residue 13961. -/
theorem bounds_15_13961 : exactInterval 15 13961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13961 : oddCount 13961 15 = 10 ∧ acceleratedOrbit 15 13961 = 25163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13961) = 3 ^ 10 * m + 25163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13961.1, data_15_13961.2]

/-- Complete interval computation for depth 15, residue 13962. -/
theorem bounds_15_13962 : exactInterval 15 13962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13962 : oddCount 13962 15 = 7 ∧ acceleratedOrbit 15 13962 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13962) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13962.1, data_15_13962.2]

/-- Complete interval computation for depth 15, residue 13963. -/
theorem bounds_15_13963 : exactInterval 15 13963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13963 : oddCount 13963 15 = 8 ∧ acceleratedOrbit 15 13963 = 2798 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13963) = 3 ^ 8 * m + 2798 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13963.1, data_15_13963.2]

/-- Complete interval computation for depth 15, residue 13964. -/
theorem bounds_15_13964 : exactInterval 15 13964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13964 : oddCount 13964 15 = 7 ∧ acceleratedOrbit 15 13964 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13964) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13964.1, data_15_13964.2]

/-- Complete interval computation for depth 15, residue 13965. -/
theorem bounds_15_13965 : exactInterval 15 13965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13965 : oddCount 13965 15 = 7 ∧ acceleratedOrbit 15 13965 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13965) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13965.1, data_15_13965.2]

/-- Complete interval computation for depth 15, residue 13966. -/
theorem bounds_15_13966 : exactInterval 15 13966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13966 : oddCount 13966 15 = 8 ∧ acceleratedOrbit 15 13966 = 2797 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13966) = 3 ^ 8 * m + 2797 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13966.1, data_15_13966.2]

/-- Complete interval computation for depth 15, residue 13967. -/
theorem bounds_15_13967 : exactInterval 15 13967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13967 : oddCount 13967 15 = 8 ∧ acceleratedOrbit 15 13967 = 2797 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13967) = 3 ^ 8 * m + 2797 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13967.1, data_15_13967.2]

/-- Complete interval computation for depth 15, residue 13968. -/
theorem bounds_15_13968 : exactInterval 15 13968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13968 : oddCount 13968 15 = 7 ∧ acceleratedOrbit 15 13968 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13968) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13968.1, data_15_13968.2]

/-- Complete interval computation for depth 15, residue 13969. -/
theorem bounds_15_13969 : exactInterval 15 13969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13969 : oddCount 13969 15 = 6 ∧ acceleratedOrbit 15 13969 = 311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13969) = 3 ^ 6 * m + 311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13969.1, data_15_13969.2]

/-- Complete interval computation for depth 15, residue 13970. -/
theorem bounds_15_13970 : exactInterval 15 13970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13970 : oddCount 13970 15 = 6 ∧ acceleratedOrbit 15 13970 = 311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13970) = 3 ^ 6 * m + 311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13970.1, data_15_13970.2]

/-- Complete interval computation for depth 15, residue 13971. -/
theorem bounds_15_13971 : exactInterval 15 13971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13971 : oddCount 13971 15 = 6 ∧ acceleratedOrbit 15 13971 = 311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13971) = 3 ^ 6 * m + 311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13971.1, data_15_13971.2]

/-- Complete interval computation for depth 15, residue 13972. -/
theorem bounds_15_13972 : exactInterval 15 13972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13972 : oddCount 13972 15 = 7 ∧ acceleratedOrbit 15 13972 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13972) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13972.1, data_15_13972.2]

/-- Complete interval computation for depth 15, residue 13973. -/
theorem bounds_15_13973 : exactInterval 15 13973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13973 : oddCount 13973 15 = 7 ∧ acceleratedOrbit 15 13973 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13973) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13973.1, data_15_13973.2]

/-- Complete interval computation for depth 15, residue 13974. -/
theorem bounds_15_13974 : exactInterval 15 13974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13974 : oddCount 13974 15 = 7 ∧ acceleratedOrbit 15 13974 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13974) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13974.1, data_15_13974.2]

/-- Complete interval computation for depth 15, residue 13975. -/
theorem bounds_15_13975 : exactInterval 15 13975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13975 : oddCount 13975 15 = 7 ∧ acceleratedOrbit 15 13975 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13975) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13975.1, data_15_13975.2]

/-- Complete interval computation for depth 15, residue 13976. -/
theorem bounds_15_13976 : exactInterval 15 13976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13976 : oddCount 13976 15 = 7 ∧ acceleratedOrbit 15 13976 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13976) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13976.1, data_15_13976.2]

/-- Complete interval computation for depth 15, residue 13977. -/
theorem bounds_15_13977 : exactInterval 15 13977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13977 : oddCount 13977 15 = 9 ∧ acceleratedOrbit 15 13977 = 8399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13977) = 3 ^ 9 * m + 8399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13977.1, data_15_13977.2]

/-- Complete interval computation for depth 15, residue 13978. -/
theorem bounds_15_13978 : exactInterval 15 13978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13978 : oddCount 13978 15 = 7 ∧ acceleratedOrbit 15 13978 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13978) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13978.1, data_15_13978.2]

/-- Complete interval computation for depth 15, residue 13979. -/
theorem bounds_15_13979 : exactInterval 15 13979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13979 : oddCount 13979 15 = 9 ∧ acceleratedOrbit 15 13979 = 8398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13979) = 3 ^ 9 * m + 8398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13979.1, data_15_13979.2]

/-- Complete interval computation for depth 15, residue 13980. -/
theorem bounds_15_13980 : exactInterval 15 13980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13980 : oddCount 13980 15 = 8 ∧ acceleratedOrbit 15 13980 = 2801 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13980) = 3 ^ 8 * m + 2801 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13980.1, data_15_13980.2]

/-- Complete interval computation for depth 15, residue 13981. -/
theorem bounds_15_13981 : exactInterval 15 13981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13981 : oddCount 13981 15 = 8 ∧ acceleratedOrbit 15 13981 = 2801 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13981) = 3 ^ 8 * m + 2801 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13981.1, data_15_13981.2]

/-- Complete interval computation for depth 15, residue 13982. -/
theorem bounds_15_13982 : exactInterval 15 13982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13982 : oddCount 13982 15 = 8 ∧ acceleratedOrbit 15 13982 = 2801 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13982) = 3 ^ 8 * m + 2801 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13982.1, data_15_13982.2]

/-- Complete interval computation for depth 15, residue 13983. -/
theorem bounds_15_13983 : exactInterval 15 13983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13983 : oddCount 13983 15 = 13 ∧ acceleratedOrbit 15 13983 = 680399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13983) = 3 ^ 13 * m + 680399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13983.1, data_15_13983.2]

/-- Complete interval computation for depth 15, residue 13984. -/
theorem bounds_15_13984 : exactInterval 15 13984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13984 : oddCount 13984 15 = 5 ∧ acceleratedOrbit 15 13984 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13984) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13984.1, data_15_13984.2]

/-- Complete interval computation for depth 15, residue 13985. -/
theorem bounds_15_13985 : exactInterval 15 13985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13985 : oddCount 13985 15 = 8 ∧ acceleratedOrbit 15 13985 = 2801 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13985) = 3 ^ 8 * m + 2801 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13985.1, data_15_13985.2]

/-- Complete interval computation for depth 15, residue 13986. -/
theorem bounds_15_13986 : exactInterval 15 13986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13986 : oddCount 13986 15 = 7 ∧ acceleratedOrbit 15 13986 = 934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13986) = 3 ^ 7 * m + 934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13986.1, data_15_13986.2]

/-- Complete interval computation for depth 15, residue 13987. -/
theorem bounds_15_13987 : exactInterval 15 13987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13987 : oddCount 13987 15 = 7 ∧ acceleratedOrbit 15 13987 = 934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13987) = 3 ^ 7 * m + 934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13987.1, data_15_13987.2]

/-- Complete interval computation for depth 15, residue 13988. -/
theorem bounds_15_13988 : exactInterval 15 13988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13988 : oddCount 13988 15 = 7 ∧ acceleratedOrbit 15 13988 = 934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13988) = 3 ^ 7 * m + 934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13988.1, data_15_13988.2]

/-- Complete interval computation for depth 15, residue 13989. -/
theorem bounds_15_13989 : exactInterval 15 13989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13989 : oddCount 13989 15 = 7 ∧ acceleratedOrbit 15 13989 = 934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13989) = 3 ^ 7 * m + 934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13989.1, data_15_13989.2]

/-- Complete interval computation for depth 15, residue 13990. -/
theorem bounds_15_13990 : exactInterval 15 13990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13990 : oddCount 13990 15 = 7 ∧ acceleratedOrbit 15 13990 = 934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13990) = 3 ^ 7 * m + 934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13990.1, data_15_13990.2]

end Collatz.Research.PassageAtlas.Batch0427
