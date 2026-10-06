import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0596

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1971. -/
theorem bounds_13_1971 : exactInterval 13 1971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1971 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1971) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1971 : oddCount 1971 13 = 4 ∧ acceleratedOrbit 13 1971 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1971 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1971) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1971.1, data_13_1971.2]

/-- Complete interval computation for depth 13, residue 1972. -/
theorem bounds_13_1972 : exactInterval 13 1972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1972 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1972) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1972 : oddCount 1972 13 = 5 ∧ acceleratedOrbit 13 1972 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1972 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1972) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1972.1, data_13_1972.2]

/-- Complete interval computation for depth 13, residue 1973. -/
theorem bounds_13_1973 : exactInterval 13 1973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1973 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1973) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1973 : oddCount 1973 13 = 5 ∧ acceleratedOrbit 13 1973 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1973 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1973) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1973.1, data_13_1973.2]

/-- Complete interval computation for depth 13, residue 1974. -/
theorem bounds_13_1974 : exactInterval 13 1974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1974 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1974) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1974 : oddCount 1974 13 = 6 ∧ acceleratedOrbit 13 1974 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1974 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1974) = 3 ^ 6 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1974.1, data_13_1974.2]

/-- Complete interval computation for depth 13, residue 1975. -/
theorem bounds_13_1975 : exactInterval 13 1975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1975 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1975) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1975 : oddCount 1975 13 = 6 ∧ acceleratedOrbit 13 1975 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1975 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1975) = 3 ^ 6 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1975.1, data_13_1975.2]

/-- Complete interval computation for depth 13, residue 1976. -/
theorem bounds_13_1976 : exactInterval 13 1976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1976 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1976) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1976 : oddCount 1976 13 = 5 ∧ acceleratedOrbit 13 1976 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1976 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1976) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1976.1, data_13_1976.2]

/-- Complete interval computation for depth 13, residue 1977. -/
theorem bounds_13_1977 : exactInterval 13 1977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1977 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1977) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1977 : oddCount 1977 13 = 7 ∧ acceleratedOrbit 13 1977 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1977 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1977) = 3 ^ 7 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1977.1, data_13_1977.2]

/-- Complete interval computation for depth 13, residue 1978. -/
theorem bounds_13_1978 : exactInterval 13 1978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1978 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1978) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1978 : oddCount 1978 13 = 5 ∧ acceleratedOrbit 13 1978 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1978 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1978) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1978.1, data_13_1978.2]

/-- Complete interval computation for depth 13, residue 1979. -/
theorem bounds_13_1979 : exactInterval 13 1979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1979 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1979) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1979 : oddCount 1979 13 = 7 ∧ acceleratedOrbit 13 1979 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1979 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1979) = 3 ^ 7 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1979.1, data_13_1979.2]

/-- Complete interval computation for depth 13, residue 1980. -/
theorem bounds_13_1980 : exactInterval 13 1980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1980 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1980) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1980 : oddCount 1980 13 = 9 ∧ acceleratedOrbit 13 1980 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1980 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1980) = 3 ^ 9 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1980.1, data_13_1980.2]

/-- Complete interval computation for depth 13, residue 1981. -/
theorem bounds_13_1981 : exactInterval 13 1981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1981 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1981) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1981 : oddCount 1981 13 = 9 ∧ acceleratedOrbit 13 1981 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1981 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1981) = 3 ^ 9 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1981.1, data_13_1981.2]

/-- Complete interval computation for depth 13, residue 1982. -/
theorem bounds_13_1982 : exactInterval 13 1982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1982 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1982) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1982 : oddCount 1982 13 = 9 ∧ acceleratedOrbit 13 1982 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1982 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1982) = 3 ^ 9 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1982.1, data_13_1982.2]

/-- Complete interval computation for depth 13, residue 1983. -/
theorem bounds_13_1983 : exactInterval 13 1983 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1983 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1983) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1983 : oddCount 1983 13 = 8 ∧ acceleratedOrbit 13 1983 = 1589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1983 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1983) = 3 ^ 8 * m + 1589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1983.1, data_13_1983.2]

/-- Complete interval computation for depth 13, residue 1984. -/
theorem bounds_13_1984 : exactInterval 13 1984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1984 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1984) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1984 : oddCount 1984 13 = 6 ∧ acceleratedOrbit 13 1984 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1984 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1984) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1984.1, data_13_1984.2]

/-- Complete interval computation for depth 13, residue 1985. -/
theorem bounds_13_1985 : exactInterval 13 1985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1985 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1985) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1985 : oddCount 1985 13 = 5 ∧ acceleratedOrbit 13 1985 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1985 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1985) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1985.1, data_13_1985.2]

end Collatz.Research.StoppingAtlas.Batch0596
