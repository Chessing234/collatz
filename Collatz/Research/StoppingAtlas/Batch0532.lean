import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0532

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 988. -/
theorem bounds_13_988 : exactInterval 13 988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_988 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 988) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_988 : oddCount 988 13 = 6 ∧ acceleratedOrbit 13 988 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_988 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 988) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_988.1, data_13_988.2]

/-- Complete interval computation for depth 13, residue 989. -/
theorem bounds_13_989 : exactInterval 13 989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_989 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 989) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_989 : oddCount 989 13 = 6 ∧ acceleratedOrbit 13 989 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_989 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 989) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_989.1, data_13_989.2]

/-- Complete interval computation for depth 13, residue 990. -/
theorem bounds_13_990 : exactInterval 13 990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_990 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 990) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_990 : oddCount 990 13 = 10 ∧ acceleratedOrbit 13 990 = 7154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_990 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 990) = 3 ^ 10 * m + 7154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_990.1, data_13_990.2]

/-- Complete interval computation for depth 13, residue 991. -/
theorem bounds_13_991 : exactInterval 13 991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_991 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 991) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_991 : oddCount 991 13 = 10 ∧ acceleratedOrbit 13 991 = 7154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_991 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 991) = 3 ^ 10 * m + 7154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_991.1, data_13_991.2]

/-- Complete interval computation for depth 13, residue 992. -/
theorem bounds_13_992 : exactInterval 13 992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_992 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 992) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_992 : oddCount 992 13 = 6 ∧ acceleratedOrbit 13 992 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_992 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 992) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_992.1, data_13_992.2]

/-- Complete interval computation for depth 13, residue 993. -/
theorem bounds_13_993 : exactInterval 13 993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_993 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 993) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_993 : oddCount 993 13 = 9 ∧ acceleratedOrbit 13 993 = 2393 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_993 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 993) = 3 ^ 9 * m + 2393 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_993.1, data_13_993.2]

/-- Complete interval computation for depth 13, residue 994. -/
theorem bounds_13_994 : exactInterval 13 994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_994 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 994) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_994 : oddCount 994 13 = 4 ∧ acceleratedOrbit 13 994 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_994 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 994) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_994.1, data_13_994.2]

/-- Complete interval computation for depth 13, residue 995. -/
theorem bounds_13_995 : exactInterval 13 995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_995 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 995) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_995 : oddCount 995 13 = 4 ∧ acceleratedOrbit 13 995 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_995 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 995) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_995.1, data_13_995.2]

/-- Complete interval computation for depth 13, residue 996. -/
theorem bounds_13_996 : exactInterval 13 996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_996 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 996) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_996 : oddCount 996 13 = 7 ∧ acceleratedOrbit 13 996 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_996 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 996) = 3 ^ 7 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_996.1, data_13_996.2]

/-- Complete interval computation for depth 13, residue 997. -/
theorem bounds_13_997 : exactInterval 13 997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_997 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 997) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_997 : oddCount 997 13 = 7 ∧ acceleratedOrbit 13 997 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_997 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 997) = 3 ^ 7 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_997.1, data_13_997.2]

/-- Complete interval computation for depth 13, residue 998. -/
theorem bounds_13_998 : exactInterval 13 998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_998 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 998) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_998 : oddCount 998 13 = 7 ∧ acceleratedOrbit 13 998 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_998 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 998) = 3 ^ 7 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_998.1, data_13_998.2]

/-- Complete interval computation for depth 13, residue 999. -/
theorem bounds_13_999 : exactInterval 13 999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_999 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 999) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_999 : oddCount 999 13 = 6 ∧ acceleratedOrbit 13 999 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_999 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 999) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_999.1, data_13_999.2]

/-- Complete interval computation for depth 13, residue 1000. -/
theorem bounds_13_1000 : exactInterval 13 1000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1000 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1000) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1000 : oddCount 1000 13 = 6 ∧ acceleratedOrbit 13 1000 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1000 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1000) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1000.1, data_13_1000.2]

/-- Complete interval computation for depth 13, residue 1001. -/
theorem bounds_13_1001 : exactInterval 13 1001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1001 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1001) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1001 : oddCount 1001 13 = 10 ∧ acceleratedOrbit 13 1001 = 7229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1001 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1001) = 3 ^ 10 * m + 7229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1001.1, data_13_1001.2]

/-- Complete interval computation for depth 13, residue 1002. -/
theorem bounds_13_1002 : exactInterval 13 1002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1002 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1002) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1002 : oddCount 1002 13 = 6 ∧ acceleratedOrbit 13 1002 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1002 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1002) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1002.1, data_13_1002.2]

end Collatz.Research.StoppingAtlas.Batch0532
