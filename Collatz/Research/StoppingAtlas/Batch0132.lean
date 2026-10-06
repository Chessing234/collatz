import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0132

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 988. -/
theorem bounds_11_988 : exactInterval 11 988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_988 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 988) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_988 : oddCount 988 11 = 5 ∧ acceleratedOrbit 11 988 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_988 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 988) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_988.1, data_11_988.2]

/-- Complete interval computation for depth 11, residue 989. -/
theorem bounds_11_989 : exactInterval 11 989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_989 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 989) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_989 : oddCount 989 11 = 5 ∧ acceleratedOrbit 11 989 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_989 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 989) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_989.1, data_11_989.2]

/-- Complete interval computation for depth 11, residue 990. -/
theorem bounds_11_990 : exactInterval 11 990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_990 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 990) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_990 : oddCount 990 11 = 8 ∧ acceleratedOrbit 11 990 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_990 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 990) = 3 ^ 8 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_990.1, data_11_990.2]

/-- Complete interval computation for depth 11, residue 991. -/
theorem bounds_11_991 : exactInterval 11 991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_991 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 991) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_991 : oddCount 991 11 = 8 ∧ acceleratedOrbit 11 991 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_991 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 991) = 3 ^ 8 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_991.1, data_11_991.2]

/-- Complete interval computation for depth 11, residue 992. -/
theorem bounds_11_992 : exactInterval 11 992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_992 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 992) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_992 : oddCount 992 11 = 5 ∧ acceleratedOrbit 11 992 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_992 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 992) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_992.1, data_11_992.2]

/-- Complete interval computation for depth 11, residue 993. -/
theorem bounds_11_993 : exactInterval 11 993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_993 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 993) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_993 : oddCount 993 11 = 7 ∧ acceleratedOrbit 11 993 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_993 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 993) = 3 ^ 7 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_993.1, data_11_993.2]

/-- Complete interval computation for depth 11, residue 994. -/
theorem bounds_11_994 : exactInterval 11 994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_994 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 994) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_994 : oddCount 994 11 = 4 ∧ acceleratedOrbit 11 994 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_994 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 994) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_994.1, data_11_994.2]

/-- Complete interval computation for depth 11, residue 995. -/
theorem bounds_11_995 : exactInterval 11 995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_995 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 995) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_995 : oddCount 995 11 = 4 ∧ acceleratedOrbit 11 995 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_995 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 995) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_995.1, data_11_995.2]

/-- Complete interval computation for depth 11, residue 996. -/
theorem bounds_11_996 : exactInterval 11 996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_996 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 996) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_996 : oddCount 996 11 = 5 ∧ acceleratedOrbit 11 996 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_996 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 996) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_996.1, data_11_996.2]

/-- Complete interval computation for depth 11, residue 997. -/
theorem bounds_11_997 : exactInterval 11 997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_997 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 997) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_997 : oddCount 997 11 = 5 ∧ acceleratedOrbit 11 997 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_997 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 997) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_997.1, data_11_997.2]

/-- Complete interval computation for depth 11, residue 998. -/
theorem bounds_11_998 : exactInterval 11 998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_998 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 998) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_998 : oddCount 998 11 = 5 ∧ acceleratedOrbit 11 998 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_998 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 998) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_998.1, data_11_998.2]

/-- Complete interval computation for depth 11, residue 999. -/
theorem bounds_11_999 : exactInterval 11 999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_999 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 999) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_999 : oddCount 999 11 = 6 ∧ acceleratedOrbit 11 999 = 356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_999 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 999) = 3 ^ 6 * m + 356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_999.1, data_11_999.2]

/-- Complete interval computation for depth 11, residue 1000. -/
theorem bounds_11_1000 : exactInterval 11 1000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1000 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1000) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1000 : oddCount 1000 11 = 5 ∧ acceleratedOrbit 11 1000 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1000 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1000) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1000.1, data_11_1000.2]

/-- Complete interval computation for depth 11, residue 1001. -/
theorem bounds_11_1001 : exactInterval 11 1001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1001 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1001) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1001 : oddCount 1001 11 = 9 ∧ acceleratedOrbit 11 1001 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1001 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1001) = 3 ^ 9 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1001.1, data_11_1001.2]

/-- Complete interval computation for depth 11, residue 1002. -/
theorem bounds_11_1002 : exactInterval 11 1002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1002 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1002) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1002 : oddCount 1002 11 = 5 ∧ acceleratedOrbit 11 1002 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1002 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1002) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1002.1, data_11_1002.2]

end Collatz.Research.StoppingAtlas.Batch0132
