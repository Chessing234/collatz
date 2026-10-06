import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0065

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 983. -/
theorem bounds_10_983 : exactInterval 10 983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_983 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 983) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_983 : oddCount 983 10 = 7 ∧ acceleratedOrbit 10 983 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_983 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 983) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_983.1, data_10_983.2]

/-- Complete interval computation for depth 10, residue 984. -/
theorem bounds_10_984 : exactInterval 10 984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_984 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 984) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_984 : oddCount 984 10 = 5 ∧ acceleratedOrbit 10 984 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_984 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 984) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_984.1, data_10_984.2]

/-- Complete interval computation for depth 10, residue 985. -/
theorem bounds_10_985 : exactInterval 10 985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_985 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 985) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_985 : oddCount 985 10 = 3 ∧ acceleratedOrbit 10 985 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_985 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 985) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_985.1, data_10_985.2]

/-- Complete interval computation for depth 10, residue 986. -/
theorem bounds_10_986 : exactInterval 10 986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_986 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 986) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_986 : oddCount 986 10 = 5 ∧ acceleratedOrbit 10 986 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_986 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 986) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_986.1, data_10_986.2]

/-- Complete interval computation for depth 10, residue 987. -/
theorem bounds_10_987 : exactInterval 10 987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_987 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 987) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_987 : oddCount 987 10 = 6 ∧ acceleratedOrbit 10 987 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_987 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 987) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_987.1, data_10_987.2]

/-- Complete interval computation for depth 10, residue 988. -/
theorem bounds_10_988 : exactInterval 10 988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_988 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 988) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_988 : oddCount 988 10 = 5 ∧ acceleratedOrbit 10 988 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_988 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 988) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_988.1, data_10_988.2]

/-- Complete interval computation for depth 10, residue 989. -/
theorem bounds_10_989 : exactInterval 10 989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_989 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 989) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_989 : oddCount 989 10 = 5 ∧ acceleratedOrbit 10 989 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_989 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 989) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_989.1, data_10_989.2]

/-- Complete interval computation for depth 10, residue 990. -/
theorem bounds_10_990 : exactInterval 10 990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_990 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 990) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_990 : oddCount 990 10 = 7 ∧ acceleratedOrbit 10 990 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_990 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 990) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_990.1, data_10_990.2]

/-- Complete interval computation for depth 10, residue 991. -/
theorem bounds_10_991 : exactInterval 10 991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_991 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 991) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_991 : oddCount 991 10 = 7 ∧ acceleratedOrbit 10 991 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_991 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 991) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_991.1, data_10_991.2]

/-- Complete interval computation for depth 10, residue 992. -/
theorem bounds_10_992 : exactInterval 10 992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_992 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 992) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_992 : oddCount 992 10 = 5 ∧ acceleratedOrbit 10 992 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_992 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 992) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_992.1, data_10_992.2]

/-- Complete interval computation for depth 10, residue 993. -/
theorem bounds_10_993 : exactInterval 10 993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_993 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 993) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_993 : oddCount 993 10 = 7 ∧ acceleratedOrbit 10 993 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_993 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 993) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_993.1, data_10_993.2]

/-- Complete interval computation for depth 10, residue 994. -/
theorem bounds_10_994 : exactInterval 10 994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_994 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 994) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_994 : oddCount 994 10 = 4 ∧ acceleratedOrbit 10 994 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_994 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 994) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_994.1, data_10_994.2]

/-- Complete interval computation for depth 10, residue 995. -/
theorem bounds_10_995 : exactInterval 10 995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_995 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 995) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_995 : oddCount 995 10 = 4 ∧ acceleratedOrbit 10 995 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_995 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 995) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_995.1, data_10_995.2]

/-- Complete interval computation for depth 10, residue 996. -/
theorem bounds_10_996 : exactInterval 10 996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_996 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 996) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_996 : oddCount 996 10 = 5 ∧ acceleratedOrbit 10 996 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_996 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 996) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_996.1, data_10_996.2]

/-- Complete interval computation for depth 10, residue 997. -/
theorem bounds_10_997 : exactInterval 10 997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_997 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 997) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_997 : oddCount 997 10 = 5 ∧ acceleratedOrbit 10 997 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_997 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 997) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_997.1, data_10_997.2]

end Collatz.Research.StoppingAtlas.Batch0065
