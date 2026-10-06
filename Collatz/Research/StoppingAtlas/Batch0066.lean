import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0066

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 998. -/
theorem bounds_10_998 : exactInterval 10 998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_998 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 998) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_998 : oddCount 998 10 = 5 ∧ acceleratedOrbit 10 998 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_998 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 998) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_998.1, data_10_998.2]

/-- Complete interval computation for depth 10, residue 999. -/
theorem bounds_10_999 : exactInterval 10 999 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_999 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 999) 10 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_999 : oddCount 999 10 = 6 ∧ acceleratedOrbit 10 999 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_999 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 999) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_999.1, data_10_999.2]

/-- Complete interval computation for depth 10, residue 1000. -/
theorem bounds_10_1000 : exactInterval 10 1000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1000 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1000) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1000 : oddCount 1000 10 = 5 ∧ acceleratedOrbit 10 1000 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1000 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1000) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1000.1, data_10_1000.2]

/-- Complete interval computation for depth 10, residue 1001. -/
theorem bounds_10_1001 : exactInterval 10 1001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1001 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1001) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1001 : oddCount 1001 10 = 8 ∧ acceleratedOrbit 10 1001 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1001 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1001) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1001.1, data_10_1001.2]

/-- Complete interval computation for depth 10, residue 1002. -/
theorem bounds_10_1002 : exactInterval 10 1002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1002 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1002) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1002 : oddCount 1002 10 = 5 ∧ acceleratedOrbit 10 1002 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1002 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1002) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1002.1, data_10_1002.2]

/-- Complete interval computation for depth 10, residue 1003. -/
theorem bounds_10_1003 : exactInterval 10 1003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1003 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1003) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1003 : oddCount 1003 10 = 7 ∧ acceleratedOrbit 10 1003 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1003 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1003) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1003.1, data_10_1003.2]

/-- Complete interval computation for depth 10, residue 1004. -/
theorem bounds_10_1004 : exactInterval 10 1004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1004 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1004) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1004 : oddCount 1004 10 = 6 ∧ acceleratedOrbit 10 1004 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1004 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1004) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1004.1, data_10_1004.2]

/-- Complete interval computation for depth 10, residue 1005. -/
theorem bounds_10_1005 : exactInterval 10 1005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1005 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1005) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1005 : oddCount 1005 10 = 6 ∧ acceleratedOrbit 10 1005 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1005 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1005) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1005.1, data_10_1005.2]

/-- Complete interval computation for depth 10, residue 1006. -/
theorem bounds_10_1006 : exactInterval 10 1006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1006 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1006) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1006 : oddCount 1006 10 = 6 ∧ acceleratedOrbit 10 1006 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1006 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1006) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1006.1, data_10_1006.2]

/-- Complete interval computation for depth 10, residue 1007. -/
theorem bounds_10_1007 : exactInterval 10 1007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1007 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1007) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1007 : oddCount 1007 10 = 7 ∧ acceleratedOrbit 10 1007 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1007 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1007) = 3 ^ 7 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1007.1, data_10_1007.2]

/-- Complete interval computation for depth 10, residue 1008. -/
theorem bounds_10_1008 : exactInterval 10 1008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1008 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1008) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1008 : oddCount 1008 10 = 6 ∧ acceleratedOrbit 10 1008 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1008 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1008) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1008.1, data_10_1008.2]

/-- Complete interval computation for depth 10, residue 1009. -/
theorem bounds_10_1009 : exactInterval 10 1009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1009 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1009) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1009 : oddCount 1009 10 = 5 ∧ acceleratedOrbit 10 1009 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1009 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1009) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1009.1, data_10_1009.2]

/-- Complete interval computation for depth 10, residue 1010. -/
theorem bounds_10_1010 : exactInterval 10 1010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1010 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1010) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1010 : oddCount 1010 10 = 6 ∧ acceleratedOrbit 10 1010 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1010 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1010) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1010.1, data_10_1010.2]

/-- Complete interval computation for depth 10, residue 1011. -/
theorem bounds_10_1011 : exactInterval 10 1011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1011 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1011) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1011 : oddCount 1011 10 = 6 ∧ acceleratedOrbit 10 1011 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1011 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1011) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1011.1, data_10_1011.2]

/-- Complete interval computation for depth 10, residue 1012. -/
theorem bounds_10_1012 : exactInterval 10 1012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1012 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1012) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1012 : oddCount 1012 10 = 6 ∧ acceleratedOrbit 10 1012 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1012 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1012) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1012.1, data_10_1012.2]

end Collatz.Research.StoppingAtlas.Batch0066
