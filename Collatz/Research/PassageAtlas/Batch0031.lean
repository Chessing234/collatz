import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0031

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 983. -/
theorem bounds_15_983 : exactInterval 15 983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_983 : oddCount 983 15 = 10 ∧ acceleratedOrbit 15 983 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 983) = 3 ^ 10 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_983.1, data_15_983.2]

/-- Complete interval computation for depth 15, residue 984. -/
theorem bounds_15_984 : exactInterval 15 984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_984 : oddCount 984 15 = 7 ∧ acceleratedOrbit 15 984 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 984) = 3 ^ 7 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_984.1, data_15_984.2]

/-- Complete interval computation for depth 15, residue 985. -/
theorem bounds_15_985 : exactInterval 15 985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_985 : oddCount 985 15 = 5 ∧ acceleratedOrbit 15 985 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 985) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_985.1, data_15_985.2]

/-- Complete interval computation for depth 15, residue 986. -/
theorem bounds_15_986 : exactInterval 15 986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_986 : oddCount 986 15 = 7 ∧ acceleratedOrbit 15 986 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 986) = 3 ^ 7 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_986.1, data_15_986.2]

/-- Complete interval computation for depth 15, residue 987. -/
theorem bounds_15_987 : exactInterval 15 987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_987 : oddCount 987 15 = 6 ∧ acceleratedOrbit 15 987 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 987) = 3 ^ 6 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_987.1, data_15_987.2]

/-- Complete interval computation for depth 15, residue 988. -/
theorem bounds_15_988 : exactInterval 15 988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_988 : oddCount 988 15 = 7 ∧ acceleratedOrbit 15 988 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 988) = 3 ^ 7 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_988.1, data_15_988.2]

/-- Complete interval computation for depth 15, residue 989. -/
theorem bounds_15_989 : exactInterval 15 989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_989 : oddCount 989 15 = 7 ∧ acceleratedOrbit 15 989 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 989) = 3 ^ 7 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_989.1, data_15_989.2]

/-- Complete interval computation for depth 15, residue 990. -/
theorem bounds_15_990 : exactInterval 15 990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_990 : oddCount 990 15 = 11 ∧ acceleratedOrbit 15 990 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 990) = 3 ^ 11 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_990.1, data_15_990.2]

/-- Complete interval computation for depth 15, residue 991. -/
theorem bounds_15_991 : exactInterval 15 991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_991 : oddCount 991 15 = 11 ∧ acceleratedOrbit 15 991 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 991) = 3 ^ 11 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_991.1, data_15_991.2]

/-- Complete interval computation for depth 15, residue 992. -/
theorem bounds_15_992 : exactInterval 15 992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_992 : oddCount 992 15 = 8 ∧ acceleratedOrbit 15 992 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 992) = 3 ^ 8 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_992.1, data_15_992.2]

/-- Complete interval computation for depth 15, residue 993. -/
theorem bounds_15_993 : exactInterval 15 993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_993 : oddCount 993 15 = 10 ∧ acceleratedOrbit 15 993 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 993) = 3 ^ 10 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_993.1, data_15_993.2]

/-- Complete interval computation for depth 15, residue 994. -/
theorem bounds_15_994 : exactInterval 15 994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_994 : oddCount 994 15 = 5 ∧ acceleratedOrbit 15 994 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 994) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_994.1, data_15_994.2]

/-- Complete interval computation for depth 15, residue 995. -/
theorem bounds_15_995 : exactInterval 15 995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_995 : oddCount 995 15 = 5 ∧ acceleratedOrbit 15 995 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 995) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_995.1, data_15_995.2]

/-- Complete interval computation for depth 15, residue 996. -/
theorem bounds_15_996 : exactInterval 15 996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_996 : oddCount 996 15 = 8 ∧ acceleratedOrbit 15 996 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 996) = 3 ^ 8 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_996.1, data_15_996.2]

/-- Complete interval computation for depth 15, residue 997. -/
theorem bounds_15_997 : exactInterval 15 997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_997 : oddCount 997 15 = 8 ∧ acceleratedOrbit 15 997 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 997) = 3 ^ 8 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_997.1, data_15_997.2]

/-- Complete interval computation for depth 15, residue 998. -/
theorem bounds_15_998 : exactInterval 15 998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_998 : oddCount 998 15 = 8 ∧ acceleratedOrbit 15 998 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 998) = 3 ^ 8 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_998.1, data_15_998.2]

/-- Complete interval computation for depth 15, residue 999. -/
theorem bounds_15_999 : exactInterval 15 999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_999 : oddCount 999 15 = 7 ∧ acceleratedOrbit 15 999 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 999) = 3 ^ 7 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_999.1, data_15_999.2]

/-- Complete interval computation for depth 15, residue 1000. -/
theorem bounds_15_1000 : exactInterval 15 1000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1000 : oddCount 1000 15 = 8 ∧ acceleratedOrbit 15 1000 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1000) = 3 ^ 8 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1000.1, data_15_1000.2]

/-- Complete interval computation for depth 15, residue 1001. -/
theorem bounds_15_1001 : exactInterval 15 1001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1001 : oddCount 1001 15 = 11 ∧ acceleratedOrbit 15 1001 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1001) = 3 ^ 11 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1001.1, data_15_1001.2]

/-- Complete interval computation for depth 15, residue 1002. -/
theorem bounds_15_1002 : exactInterval 15 1002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1002 : oddCount 1002 15 = 8 ∧ acceleratedOrbit 15 1002 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1002) = 3 ^ 8 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1002.1, data_15_1002.2]

/-- Complete interval computation for depth 15, residue 1003. -/
theorem bounds_15_1003 : exactInterval 15 1003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1003 : oddCount 1003 15 = 9 ∧ acceleratedOrbit 15 1003 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1003) = 3 ^ 9 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1003.1, data_15_1003.2]

/-- Complete interval computation for depth 15, residue 1004. -/
theorem bounds_15_1004 : exactInterval 15 1004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1004 : oddCount 1004 15 = 10 ∧ acceleratedOrbit 15 1004 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1004) = 3 ^ 10 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1004.1, data_15_1004.2]

/-- Complete interval computation for depth 15, residue 1005. -/
theorem bounds_15_1005 : exactInterval 15 1005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1005 : oddCount 1005 15 = 10 ∧ acceleratedOrbit 15 1005 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1005) = 3 ^ 10 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1005.1, data_15_1005.2]

/-- Complete interval computation for depth 15, residue 1006. -/
theorem bounds_15_1006 : exactInterval 15 1006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1006 : oddCount 1006 15 = 10 ∧ acceleratedOrbit 15 1006 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1006) = 3 ^ 10 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1006.1, data_15_1006.2]

/-- Complete interval computation for depth 15, residue 1007. -/
theorem bounds_15_1007 : exactInterval 15 1007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1007 : oddCount 1007 15 = 11 ∧ acceleratedOrbit 15 1007 = 5453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1007) = 3 ^ 11 * m + 5453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1007.1, data_15_1007.2]

/-- Complete interval computation for depth 15, residue 1008. -/
theorem bounds_15_1008 : exactInterval 15 1008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1008 : oddCount 1008 15 = 8 ∧ acceleratedOrbit 15 1008 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1008) = 3 ^ 8 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1008.1, data_15_1008.2]

/-- Complete interval computation for depth 15, residue 1009. -/
theorem bounds_15_1009 : exactInterval 15 1009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1009 : oddCount 1009 15 = 8 ∧ acceleratedOrbit 15 1009 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1009) = 3 ^ 8 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1009.1, data_15_1009.2]

/-- Complete interval computation for depth 15, residue 1010. -/
theorem bounds_15_1010 : exactInterval 15 1010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1010 : oddCount 1010 15 = 9 ∧ acceleratedOrbit 15 1010 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1010) = 3 ^ 9 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1010.1, data_15_1010.2]

/-- Complete interval computation for depth 15, residue 1011. -/
theorem bounds_15_1011 : exactInterval 15 1011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1011 : oddCount 1011 15 = 9 ∧ acceleratedOrbit 15 1011 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1011) = 3 ^ 9 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1011.1, data_15_1011.2]

/-- Complete interval computation for depth 15, residue 1012. -/
theorem bounds_15_1012 : exactInterval 15 1012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1012 : oddCount 1012 15 = 8 ∧ acceleratedOrbit 15 1012 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1012) = 3 ^ 8 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1012.1, data_15_1012.2]

/-- Complete interval computation for depth 15, residue 1013. -/
theorem bounds_15_1013 : exactInterval 15 1013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1013 : oddCount 1013 15 = 8 ∧ acceleratedOrbit 15 1013 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1013) = 3 ^ 8 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1013.1, data_15_1013.2]

/-- Complete interval computation for depth 15, residue 1014. -/
theorem bounds_15_1014 : exactInterval 15 1014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1014 : oddCount 1014 15 = 7 ∧ acceleratedOrbit 15 1014 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1014) = 3 ^ 7 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1014.1, data_15_1014.2]

end Collatz.Research.PassageAtlas.Batch0031
