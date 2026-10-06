import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0329

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1966. -/
theorem bounds_12_1966 : exactInterval 12 1966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1966 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1966) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1966 : oddCount 1966 12 = 8 ∧ acceleratedOrbit 12 1966 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1966 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1966) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1966.1, data_12_1966.2]

/-- Complete interval computation for depth 12, residue 1967. -/
theorem bounds_12_1967 : exactInterval 12 1967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1967 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1967) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1967 : oddCount 1967 12 = 7 ∧ acceleratedOrbit 12 1967 = 1052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1967 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1967) = 3 ^ 7 * m + 1052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1967.1, data_12_1967.2]

/-- Complete interval computation for depth 12, residue 1968. -/
theorem bounds_12_1968 : exactInterval 12 1968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1968 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1968) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1968 : oddCount 1968 12 = 5 ∧ acceleratedOrbit 12 1968 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1968 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1968) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1968.1, data_12_1968.2]

/-- Complete interval computation for depth 12, residue 1969. -/
theorem bounds_12_1969 : exactInterval 12 1969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1969 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1969) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1969 : oddCount 1969 12 = 3 ∧ acceleratedOrbit 12 1969 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1969 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1969) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1969.1, data_12_1969.2]

/-- Complete interval computation for depth 12, residue 1970. -/
theorem bounds_12_1970 : exactInterval 12 1970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1970 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1970) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1970 : oddCount 1970 12 = 3 ∧ acceleratedOrbit 12 1970 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1970 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1970) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1970.1, data_12_1970.2]

/-- Complete interval computation for depth 12, residue 1971. -/
theorem bounds_12_1971 : exactInterval 12 1971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1971 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1971) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1971 : oddCount 1971 12 = 3 ∧ acceleratedOrbit 12 1971 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1971 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1971) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1971.1, data_12_1971.2]

/-- Complete interval computation for depth 12, residue 1972. -/
theorem bounds_12_1972 : exactInterval 12 1972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1972 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1972) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1972 : oddCount 1972 12 = 5 ∧ acceleratedOrbit 12 1972 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1972 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1972) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1972.1, data_12_1972.2]

/-- Complete interval computation for depth 12, residue 1973. -/
theorem bounds_12_1973 : exactInterval 12 1973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1973 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1973) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1973 : oddCount 1973 12 = 5 ∧ acceleratedOrbit 12 1973 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1973 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1973) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1973.1, data_12_1973.2]

/-- Complete interval computation for depth 12, residue 1974. -/
theorem bounds_12_1974 : exactInterval 12 1974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1974 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1974) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1974 : oddCount 1974 12 = 6 ∧ acceleratedOrbit 12 1974 = 352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1974 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1974) = 3 ^ 6 * m + 352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1974.1, data_12_1974.2]

/-- Complete interval computation for depth 12, residue 1975. -/
theorem bounds_12_1975 : exactInterval 12 1975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1975 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1975) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1975 : oddCount 1975 12 = 6 ∧ acceleratedOrbit 12 1975 = 352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1975 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1975) = 3 ^ 6 * m + 352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1975.1, data_12_1975.2]

/-- Complete interval computation for depth 12, residue 1976. -/
theorem bounds_12_1976 : exactInterval 12 1976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1976 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1976) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1976 : oddCount 1976 12 = 5 ∧ acceleratedOrbit 12 1976 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1976 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1976) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1976.1, data_12_1976.2]

/-- Complete interval computation for depth 12, residue 1977. -/
theorem bounds_12_1977 : exactInterval 12 1977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1977 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1977) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1977 : oddCount 1977 12 = 6 ∧ acceleratedOrbit 12 1977 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1977 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1977) = 3 ^ 6 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1977.1, data_12_1977.2]

/-- Complete interval computation for depth 12, residue 1978. -/
theorem bounds_12_1978 : exactInterval 12 1978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1978 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1978) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1978 : oddCount 1978 12 = 5 ∧ acceleratedOrbit 12 1978 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1978 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1978) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1978.1, data_12_1978.2]

/-- Complete interval computation for depth 12, residue 1979. -/
theorem bounds_12_1979 : exactInterval 12 1979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1979 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1979) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1979 : oddCount 1979 12 = 6 ∧ acceleratedOrbit 12 1979 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1979 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1979) = 3 ^ 6 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1979.1, data_12_1979.2]

/-- Complete interval computation for depth 12, residue 1980. -/
theorem bounds_12_1980 : exactInterval 12 1980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1980 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1980) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1980 : oddCount 1980 12 = 8 ∧ acceleratedOrbit 12 1980 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1980 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1980) = 3 ^ 8 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1980.1, data_12_1980.2]

end Collatz.Research.StoppingAtlas.Batch0329
