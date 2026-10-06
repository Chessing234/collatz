import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0265

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 983. -/
theorem bounds_12_983 : exactInterval 12 983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_983 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 983) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_983 : oddCount 983 12 = 8 ∧ acceleratedOrbit 12 983 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_983 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 983) = 3 ^ 8 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_983.1, data_12_983.2]

/-- Complete interval computation for depth 12, residue 984. -/
theorem bounds_12_984 : exactInterval 12 984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_984 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 984) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_984 : oddCount 984 12 = 5 ∧ acceleratedOrbit 12 984 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_984 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 984) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_984.1, data_12_984.2]

/-- Complete interval computation for depth 12, residue 985. -/
theorem bounds_12_985 : exactInterval 12 985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_985 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 985) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_985 : oddCount 985 12 = 4 ∧ acceleratedOrbit 12 985 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_985 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 985) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_985.1, data_12_985.2]

/-- Complete interval computation for depth 12, residue 986. -/
theorem bounds_12_986 : exactInterval 12 986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_986 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 986) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_986 : oddCount 986 12 = 5 ∧ acceleratedOrbit 12 986 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_986 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 986) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_986.1, data_12_986.2]

/-- Complete interval computation for depth 12, residue 987. -/
theorem bounds_12_987 : exactInterval 12 987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_987 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 987) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_987 : oddCount 987 12 = 6 ∧ acceleratedOrbit 12 987 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_987 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 987) = 3 ^ 6 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_987.1, data_12_987.2]

/-- Complete interval computation for depth 12, residue 988. -/
theorem bounds_12_988 : exactInterval 12 988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_988 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 988) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_988 : oddCount 988 12 = 5 ∧ acceleratedOrbit 12 988 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_988 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 988) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_988.1, data_12_988.2]

/-- Complete interval computation for depth 12, residue 989. -/
theorem bounds_12_989 : exactInterval 12 989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_989 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 989) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_989 : oddCount 989 12 = 5 ∧ acceleratedOrbit 12 989 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_989 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 989) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_989.1, data_12_989.2]

/-- Complete interval computation for depth 12, residue 990. -/
theorem bounds_12_990 : exactInterval 12 990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_990 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 990) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_990 : oddCount 990 12 = 9 ∧ acceleratedOrbit 12 990 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_990 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 990) = 3 ^ 9 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_990.1, data_12_990.2]

/-- Complete interval computation for depth 12, residue 991. -/
theorem bounds_12_991 : exactInterval 12 991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_991 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 991) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_991 : oddCount 991 12 = 9 ∧ acceleratedOrbit 12 991 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_991 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 991) = 3 ^ 9 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_991.1, data_12_991.2]

/-- Complete interval computation for depth 12, residue 992. -/
theorem bounds_12_992 : exactInterval 12 992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_992 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 992) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_992 : oddCount 992 12 = 6 ∧ acceleratedOrbit 12 992 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_992 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 992) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_992.1, data_12_992.2]

/-- Complete interval computation for depth 12, residue 993. -/
theorem bounds_12_993 : exactInterval 12 993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_993 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 993) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_993 : oddCount 993 12 = 8 ∧ acceleratedOrbit 12 993 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_993 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 993) = 3 ^ 8 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_993.1, data_12_993.2]

/-- Complete interval computation for depth 12, residue 994. -/
theorem bounds_12_994 : exactInterval 12 994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_994 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 994) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_994 : oddCount 994 12 = 4 ∧ acceleratedOrbit 12 994 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_994 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 994) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_994.1, data_12_994.2]

/-- Complete interval computation for depth 12, residue 995. -/
theorem bounds_12_995 : exactInterval 12 995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_995 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 995) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_995 : oddCount 995 12 = 4 ∧ acceleratedOrbit 12 995 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_995 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 995) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_995.1, data_12_995.2]

/-- Complete interval computation for depth 12, residue 996. -/
theorem bounds_12_996 : exactInterval 12 996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_996 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 996) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_996 : oddCount 996 12 = 6 ∧ acceleratedOrbit 12 996 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_996 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 996) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_996.1, data_12_996.2]

/-- Complete interval computation for depth 12, residue 997. -/
theorem bounds_12_997 : exactInterval 12 997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_997 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 997) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_997 : oddCount 997 12 = 6 ∧ acceleratedOrbit 12 997 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_997 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 997) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_997.1, data_12_997.2]

end Collatz.Research.StoppingAtlas.Batch0265
