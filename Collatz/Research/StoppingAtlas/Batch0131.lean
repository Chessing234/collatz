import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0131

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 972. -/
theorem bounds_11_972 : exactInterval 11 972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_972 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 972) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_972 : oddCount 972 11 = 6 ∧ acceleratedOrbit 11 972 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_972 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 972) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_972.1, data_11_972.2]

/-- Complete interval computation for depth 11, residue 973. -/
theorem bounds_11_973 : exactInterval 11 973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_973 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 973) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_973 : oddCount 973 11 = 6 ∧ acceleratedOrbit 11 973 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_973 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 973) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_973.1, data_11_973.2]

/-- Complete interval computation for depth 11, residue 974. -/
theorem bounds_11_974 : exactInterval 11 974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_974 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 974) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_974 : oddCount 974 11 = 7 ∧ acceleratedOrbit 11 974 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_974 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 974) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_974.1, data_11_974.2]

/-- Complete interval computation for depth 11, residue 975. -/
theorem bounds_11_975 : exactInterval 11 975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_975 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 975) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_975 : oddCount 975 11 = 7 ∧ acceleratedOrbit 11 975 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_975 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 975) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_975.1, data_11_975.2]

/-- Complete interval computation for depth 11, residue 976. -/
theorem bounds_11_976 : exactInterval 11 976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_976 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 976) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_976 : oddCount 976 11 = 4 ∧ acceleratedOrbit 11 976 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_976 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 976) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_976.1, data_11_976.2]

/-- Complete interval computation for depth 11, residue 977. -/
theorem bounds_11_977 : exactInterval 11 977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_977 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 977) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_977 : oddCount 977 11 = 6 ∧ acceleratedOrbit 11 977 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_977 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 977) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_977.1, data_11_977.2]

/-- Complete interval computation for depth 11, residue 978. -/
theorem bounds_11_978 : exactInterval 11 978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_978 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 978) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_978 : oddCount 978 11 = 7 ∧ acceleratedOrbit 11 978 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_978 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 978) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_978.1, data_11_978.2]

/-- Complete interval computation for depth 11, residue 979. -/
theorem bounds_11_979 : exactInterval 11 979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_979 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 979) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_979 : oddCount 979 11 = 7 ∧ acceleratedOrbit 11 979 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_979 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 979) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_979.1, data_11_979.2]

/-- Complete interval computation for depth 11, residue 980. -/
theorem bounds_11_980 : exactInterval 11 980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_980 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 980) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_980 : oddCount 980 11 = 4 ∧ acceleratedOrbit 11 980 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_980 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 980) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_980.1, data_11_980.2]

/-- Complete interval computation for depth 11, residue 981. -/
theorem bounds_11_981 : exactInterval 11 981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_981 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 981) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_981 : oddCount 981 11 = 4 ∧ acceleratedOrbit 11 981 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_981 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 981) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_981.1, data_11_981.2]

/-- Complete interval computation for depth 11, residue 982. -/
theorem bounds_11_982 : exactInterval 11 982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_982 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 982) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_982 : oddCount 982 11 = 8 ∧ acceleratedOrbit 11 982 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_982 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 982) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_982.1, data_11_982.2]

/-- Complete interval computation for depth 11, residue 983. -/
theorem bounds_11_983 : exactInterval 11 983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_983 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 983) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_983 : oddCount 983 11 = 8 ∧ acceleratedOrbit 11 983 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_983 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 983) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_983.1, data_11_983.2]

/-- Complete interval computation for depth 11, residue 984. -/
theorem bounds_11_984 : exactInterval 11 984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_984 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 984) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_984 : oddCount 984 11 = 5 ∧ acceleratedOrbit 11 984 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_984 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 984) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_984.1, data_11_984.2]

/-- Complete interval computation for depth 11, residue 985. -/
theorem bounds_11_985 : exactInterval 11 985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_985 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 985) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_985 : oddCount 985 11 = 3 ∧ acceleratedOrbit 11 985 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_985 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 985) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_985.1, data_11_985.2]

/-- Complete interval computation for depth 11, residue 986. -/
theorem bounds_11_986 : exactInterval 11 986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_986 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 986) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_986 : oddCount 986 11 = 5 ∧ acceleratedOrbit 11 986 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_986 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 986) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_986.1, data_11_986.2]

/-- Complete interval computation for depth 11, residue 987. -/
theorem bounds_11_987 : exactInterval 11 987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_987 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 987) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_987 : oddCount 987 11 = 6 ∧ acceleratedOrbit 11 987 = 352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_987 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 987) = 3 ^ 6 * m + 352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_987.1, data_11_987.2]

end Collatz.Research.StoppingAtlas.Batch0131
