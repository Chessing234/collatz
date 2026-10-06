import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0196

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1971. -/
theorem bounds_11_1971 : exactInterval 11 1971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1971 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1971) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1971 : oddCount 1971 11 = 3 ∧ acceleratedOrbit 11 1971 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1971 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1971) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1971.1, data_11_1971.2]

/-- Complete interval computation for depth 11, residue 1972. -/
theorem bounds_11_1972 : exactInterval 11 1972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1972 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1972) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1972 : oddCount 1972 11 = 5 ∧ acceleratedOrbit 11 1972 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1972 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1972) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1972.1, data_11_1972.2]

/-- Complete interval computation for depth 11, residue 1973. -/
theorem bounds_11_1973 : exactInterval 11 1973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1973 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1973) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1973 : oddCount 1973 11 = 5 ∧ acceleratedOrbit 11 1973 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1973 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1973) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1973.1, data_11_1973.2]

/-- Complete interval computation for depth 11, residue 1974. -/
theorem bounds_11_1974 : exactInterval 11 1974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1974 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1974) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1974 : oddCount 1974 11 = 6 ∧ acceleratedOrbit 11 1974 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1974 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1974) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1974.1, data_11_1974.2]

/-- Complete interval computation for depth 11, residue 1975. -/
theorem bounds_11_1975 : exactInterval 11 1975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1975 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1975) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1975 : oddCount 1975 11 = 6 ∧ acceleratedOrbit 11 1975 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1975 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1975) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1975.1, data_11_1975.2]

/-- Complete interval computation for depth 11, residue 1976. -/
theorem bounds_11_1976 : exactInterval 11 1976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1976 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1976) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1976 : oddCount 1976 11 = 5 ∧ acceleratedOrbit 11 1976 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1976 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1976) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1976.1, data_11_1976.2]

/-- Complete interval computation for depth 11, residue 1977. -/
theorem bounds_11_1977 : exactInterval 11 1977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1977 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1977) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1977 : oddCount 1977 11 = 5 ∧ acceleratedOrbit 11 1977 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1977 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1977) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1977.1, data_11_1977.2]

/-- Complete interval computation for depth 11, residue 1978. -/
theorem bounds_11_1978 : exactInterval 11 1978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1978 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1978) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1978 : oddCount 1978 11 = 5 ∧ acceleratedOrbit 11 1978 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1978 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1978) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1978.1, data_11_1978.2]

/-- Complete interval computation for depth 11, residue 1979. -/
theorem bounds_11_1979 : exactInterval 11 1979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1979 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1979) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1979 : oddCount 1979 11 = 5 ∧ acceleratedOrbit 11 1979 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1979 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1979) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1979.1, data_11_1979.2]

/-- Complete interval computation for depth 11, residue 1980. -/
theorem bounds_11_1980 : exactInterval 11 1980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1980 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1980) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1980 : oddCount 1980 11 = 7 ∧ acceleratedOrbit 11 1980 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1980 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1980) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1980.1, data_11_1980.2]

/-- Complete interval computation for depth 11, residue 1981. -/
theorem bounds_11_1981 : exactInterval 11 1981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1981 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1981) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1981 : oddCount 1981 11 = 7 ∧ acceleratedOrbit 11 1981 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1981 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1981) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1981.1, data_11_1981.2]

/-- Complete interval computation for depth 11, residue 1982. -/
theorem bounds_11_1982 : exactInterval 11 1982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1982 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1982) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1982 : oddCount 1982 11 = 7 ∧ acceleratedOrbit 11 1982 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1982 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1982) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1982.1, data_11_1982.2]

/-- Complete interval computation for depth 11, residue 1983. -/
theorem bounds_11_1983 : exactInterval 11 1983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1983 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1983) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1983 : oddCount 1983 11 = 8 ∧ acceleratedOrbit 11 1983 = 6356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1983 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1983) = 3 ^ 8 * m + 6356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1983.1, data_11_1983.2]

/-- Complete interval computation for depth 11, residue 1984. -/
theorem bounds_11_1984 : exactInterval 11 1984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1984 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1984) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1984 : oddCount 1984 11 = 5 ∧ acceleratedOrbit 11 1984 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1984 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1984) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1984.1, data_11_1984.2]

/-- Complete interval computation for depth 11, residue 1985. -/
theorem bounds_11_1985 : exactInterval 11 1985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1985 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1985) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1985 : oddCount 1985 11 = 5 ∧ acceleratedOrbit 11 1985 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1985 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1985) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1985.1, data_11_1985.2]

end Collatz.Research.StoppingAtlas.Batch0196
