import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0531

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 972. -/
theorem bounds_13_972 : exactInterval 13 972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_972 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 972) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_972 : oddCount 972 13 = 7 ∧ acceleratedOrbit 13 972 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_972 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 972) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_972.1, data_13_972.2]

/-- Complete interval computation for depth 13, residue 973. -/
theorem bounds_13_973 : exactInterval 13 973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_973 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 973) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_973 : oddCount 973 13 = 7 ∧ acceleratedOrbit 13 973 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_973 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 973) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_973.1, data_13_973.2]

/-- Complete interval computation for depth 13, residue 974. -/
theorem bounds_13_974 : exactInterval 13 974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_974 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 974) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_974 : oddCount 974 13 = 9 ∧ acceleratedOrbit 13 974 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_974 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 974) = 3 ^ 9 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_974.1, data_13_974.2]

/-- Complete interval computation for depth 13, residue 975. -/
theorem bounds_13_975 : exactInterval 13 975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_975 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 975) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_975 : oddCount 975 13 = 9 ∧ acceleratedOrbit 13 975 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_975 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 975) = 3 ^ 9 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_975.1, data_13_975.2]

/-- Complete interval computation for depth 13, residue 976. -/
theorem bounds_13_976 : exactInterval 13 976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_976 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 976) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_976 : oddCount 976 13 = 4 ∧ acceleratedOrbit 13 976 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_976 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 976) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_976.1, data_13_976.2]

/-- Complete interval computation for depth 13, residue 977. -/
theorem bounds_13_977 : exactInterval 13 977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_977 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 977) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_977 : oddCount 977 13 = 7 ∧ acceleratedOrbit 13 977 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_977 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 977) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_977.1, data_13_977.2]

/-- Complete interval computation for depth 13, residue 978. -/
theorem bounds_13_978 : exactInterval 13 978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_978 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 978) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_978 : oddCount 978 13 = 7 ∧ acceleratedOrbit 13 978 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_978 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 978) = 3 ^ 7 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_978.1, data_13_978.2]

/-- Complete interval computation for depth 13, residue 979. -/
theorem bounds_13_979 : exactInterval 13 979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_979 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 979) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_979 : oddCount 979 13 = 7 ∧ acceleratedOrbit 13 979 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_979 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 979) = 3 ^ 7 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_979.1, data_13_979.2]

/-- Complete interval computation for depth 13, residue 980. -/
theorem bounds_13_980 : exactInterval 13 980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_980 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 980) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_980 : oddCount 980 13 = 4 ∧ acceleratedOrbit 13 980 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_980 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 980) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_980.1, data_13_980.2]

/-- Complete interval computation for depth 13, residue 981. -/
theorem bounds_13_981 : exactInterval 13 981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_981 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 981) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_981 : oddCount 981 13 = 4 ∧ acceleratedOrbit 13 981 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_981 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 981) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_981.1, data_13_981.2]

/-- Complete interval computation for depth 13, residue 982. -/
theorem bounds_13_982 : exactInterval 13 982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_982 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 982) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_982 : oddCount 982 13 = 9 ∧ acceleratedOrbit 13 982 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_982 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 982) = 3 ^ 9 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_982.1, data_13_982.2]

/-- Complete interval computation for depth 13, residue 983. -/
theorem bounds_13_983 : exactInterval 13 983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_983 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 983) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_983 : oddCount 983 13 = 9 ∧ acceleratedOrbit 13 983 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_983 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 983) = 3 ^ 9 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_983.1, data_13_983.2]

/-- Complete interval computation for depth 13, residue 984. -/
theorem bounds_13_984 : exactInterval 13 984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_984 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 984) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_984 : oddCount 984 13 = 6 ∧ acceleratedOrbit 13 984 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_984 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 984) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_984.1, data_13_984.2]

/-- Complete interval computation for depth 13, residue 985. -/
theorem bounds_13_985 : exactInterval 13 985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_985 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 985) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_985 : oddCount 985 13 = 4 ∧ acceleratedOrbit 13 985 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_985 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 985) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_985.1, data_13_985.2]

/-- Complete interval computation for depth 13, residue 986. -/
theorem bounds_13_986 : exactInterval 13 986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_986 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 986) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_986 : oddCount 986 13 = 6 ∧ acceleratedOrbit 13 986 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_986 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 986) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_986.1, data_13_986.2]

/-- Complete interval computation for depth 13, residue 987. -/
theorem bounds_13_987 : exactInterval 13 987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_987 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 987) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_987 : oddCount 987 13 = 6 ∧ acceleratedOrbit 13 987 = 88 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_987 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 987) = 3 ^ 6 * m + 88 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_987.1, data_13_987.2]

end Collatz.Research.StoppingAtlas.Batch0531
