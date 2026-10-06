import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0061

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1966. -/
theorem bounds_15_1966 : exactInterval 15 1966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1966 : oddCount 1966 15 = 10 ∧ acceleratedOrbit 15 1966 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1966) = 3 ^ 10 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1966.1, data_15_1966.2]

/-- Complete interval computation for depth 15, residue 1967. -/
theorem bounds_15_1967 : exactInterval 15 1967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1967 : oddCount 1967 15 = 8 ∧ acceleratedOrbit 15 1967 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1967) = 3 ^ 8 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1967.1, data_15_1967.2]

/-- Complete interval computation for depth 15, residue 1968. -/
theorem bounds_15_1968 : exactInterval 15 1968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1968 : oddCount 1968 15 = 7 ∧ acceleratedOrbit 15 1968 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1968) = 3 ^ 7 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1968.1, data_15_1968.2]

/-- Complete interval computation for depth 15, residue 1969. -/
theorem bounds_15_1969 : exactInterval 15 1969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1969 : oddCount 1969 15 = 4 ∧ acceleratedOrbit 15 1969 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1969) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1969.1, data_15_1969.2]

/-- Complete interval computation for depth 15, residue 1970. -/
theorem bounds_15_1970 : exactInterval 15 1970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1970 : oddCount 1970 15 = 4 ∧ acceleratedOrbit 15 1970 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1970) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1970.1, data_15_1970.2]

/-- Complete interval computation for depth 15, residue 1971. -/
theorem bounds_15_1971 : exactInterval 15 1971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1971 : oddCount 1971 15 = 4 ∧ acceleratedOrbit 15 1971 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1971) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1971.1, data_15_1971.2]

/-- Complete interval computation for depth 15, residue 1972. -/
theorem bounds_15_1972 : exactInterval 15 1972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1972 : oddCount 1972 15 = 7 ∧ acceleratedOrbit 15 1972 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1972) = 3 ^ 7 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1972.1, data_15_1972.2]

/-- Complete interval computation for depth 15, residue 1973. -/
theorem bounds_15_1973 : exactInterval 15 1973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1973 : oddCount 1973 15 = 7 ∧ acceleratedOrbit 15 1973 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1973) = 3 ^ 7 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1973.1, data_15_1973.2]

/-- Complete interval computation for depth 15, residue 1974. -/
theorem bounds_15_1974 : exactInterval 15 1974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1974 : oddCount 1974 15 = 6 ∧ acceleratedOrbit 15 1974 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1974) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1974.1, data_15_1974.2]

/-- Complete interval computation for depth 15, residue 1975. -/
theorem bounds_15_1975 : exactInterval 15 1975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1975 : oddCount 1975 15 = 6 ∧ acceleratedOrbit 15 1975 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1975) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1975.1, data_15_1975.2]

/-- Complete interval computation for depth 15, residue 1976. -/
theorem bounds_15_1976 : exactInterval 15 1976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1976 : oddCount 1976 15 = 7 ∧ acceleratedOrbit 15 1976 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1976) = 3 ^ 7 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1976.1, data_15_1976.2]

/-- Complete interval computation for depth 15, residue 1977. -/
theorem bounds_15_1977 : exactInterval 15 1977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1977 : oddCount 1977 15 = 8 ∧ acceleratedOrbit 15 1977 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1977) = 3 ^ 8 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1977.1, data_15_1977.2]

/-- Complete interval computation for depth 15, residue 1978. -/
theorem bounds_15_1978 : exactInterval 15 1978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1978 : oddCount 1978 15 = 7 ∧ acceleratedOrbit 15 1978 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1978) = 3 ^ 7 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1978.1, data_15_1978.2]

/-- Complete interval computation for depth 15, residue 1979. -/
theorem bounds_15_1979 : exactInterval 15 1979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1979 : oddCount 1979 15 = 8 ∧ acceleratedOrbit 15 1979 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1979) = 3 ^ 8 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1979.1, data_15_1979.2]

/-- Complete interval computation for depth 15, residue 1980. -/
theorem bounds_15_1980 : exactInterval 15 1980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1980 : oddCount 1980 15 = 10 ∧ acceleratedOrbit 15 1980 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1980) = 3 ^ 10 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1980.1, data_15_1980.2]

/-- Complete interval computation for depth 15, residue 1981. -/
theorem bounds_15_1981 : exactInterval 15 1981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1981 : oddCount 1981 15 = 10 ∧ acceleratedOrbit 15 1981 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1981) = 3 ^ 10 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1981.1, data_15_1981.2]

/-- Complete interval computation for depth 15, residue 1982. -/
theorem bounds_15_1982 : exactInterval 15 1982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1982 : oddCount 1982 15 = 10 ∧ acceleratedOrbit 15 1982 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1982) = 3 ^ 10 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1982.1, data_15_1982.2]

/-- Complete interval computation for depth 15, residue 1983. -/
theorem bounds_15_1983 : exactInterval 15 1983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1983 : oddCount 1983 15 = 9 ∧ acceleratedOrbit 15 1983 = 1192 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1983) = 3 ^ 9 * m + 1192 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1983.1, data_15_1983.2]

/-- Complete interval computation for depth 15, residue 1984. -/
theorem bounds_15_1984 : exactInterval 15 1984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1984 : oddCount 1984 15 = 7 ∧ acceleratedOrbit 15 1984 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1984) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1984.1, data_15_1984.2]

/-- Complete interval computation for depth 15, residue 1985. -/
theorem bounds_15_1985 : exactInterval 15 1985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1985 : oddCount 1985 15 = 7 ∧ acceleratedOrbit 15 1985 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1985) = 3 ^ 7 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1985.1, data_15_1985.2]

/-- Complete interval computation for depth 15, residue 1986. -/
theorem bounds_15_1986 : exactInterval 15 1986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1986 : oddCount 1986 15 = 10 ∧ acceleratedOrbit 15 1986 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1986) = 3 ^ 10 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1986.1, data_15_1986.2]

/-- Complete interval computation for depth 15, residue 1987. -/
theorem bounds_15_1987 : exactInterval 15 1987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1987 : oddCount 1987 15 = 10 ∧ acceleratedOrbit 15 1987 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1987) = 3 ^ 10 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1987.1, data_15_1987.2]

/-- Complete interval computation for depth 15, residue 1988. -/
theorem bounds_15_1988 : exactInterval 15 1988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1988 : oddCount 1988 15 = 4 ∧ acceleratedOrbit 15 1988 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1988) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1988.1, data_15_1988.2]

/-- Complete interval computation for depth 15, residue 1989. -/
theorem bounds_15_1989 : exactInterval 15 1989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1989 : oddCount 1989 15 = 4 ∧ acceleratedOrbit 15 1989 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1989) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1989.1, data_15_1989.2]

/-- Complete interval computation for depth 15, residue 1990. -/
theorem bounds_15_1990 : exactInterval 15 1990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1990 : oddCount 1990 15 = 4 ∧ acceleratedOrbit 15 1990 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1990) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1990.1, data_15_1990.2]

/-- Complete interval computation for depth 15, residue 1991. -/
theorem bounds_15_1991 : exactInterval 15 1991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1991 : oddCount 1991 15 = 7 ∧ acceleratedOrbit 15 1991 = 133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1991) = 3 ^ 7 * m + 133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1991.1, data_15_1991.2]

/-- Complete interval computation for depth 15, residue 1992. -/
theorem bounds_15_1992 : exactInterval 15 1992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1992 : oddCount 1992 15 = 8 ∧ acceleratedOrbit 15 1992 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1992) = 3 ^ 8 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1992.1, data_15_1992.2]

/-- Complete interval computation for depth 15, residue 1993. -/
theorem bounds_15_1993 : exactInterval 15 1993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1993 : oddCount 1993 15 = 8 ∧ acceleratedOrbit 15 1993 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1993) = 3 ^ 8 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1993.1, data_15_1993.2]

/-- Complete interval computation for depth 15, residue 1994. -/
theorem bounds_15_1994 : exactInterval 15 1994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1994 : oddCount 1994 15 = 8 ∧ acceleratedOrbit 15 1994 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1994) = 3 ^ 8 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1994.1, data_15_1994.2]

/-- Complete interval computation for depth 15, residue 1995. -/
theorem bounds_15_1995 : exactInterval 15 1995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1995 : oddCount 1995 15 = 8 ∧ acceleratedOrbit 15 1995 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1995) = 3 ^ 8 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1995.1, data_15_1995.2]

/-- Complete interval computation for depth 15, residue 1996. -/
theorem bounds_15_1996 : exactInterval 15 1996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1996 : oddCount 1996 15 = 8 ∧ acceleratedOrbit 15 1996 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1996) = 3 ^ 8 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1996.1, data_15_1996.2]

/-- Complete interval computation for depth 15, residue 1997. -/
theorem bounds_15_1997 : exactInterval 15 1997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1997 : oddCount 1997 15 = 8 ∧ acceleratedOrbit 15 1997 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1997) = 3 ^ 8 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1997.1, data_15_1997.2]

end Collatz.Research.PassageAtlas.Batch0061
