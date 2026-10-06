import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0266

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 998. -/
theorem bounds_12_998 : exactInterval 12 998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_998 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 998) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_998 : oddCount 998 12 = 6 ∧ acceleratedOrbit 12 998 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_998 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 998) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_998.1, data_12_998.2]

/-- Complete interval computation for depth 12, residue 999. -/
theorem bounds_12_999 : exactInterval 12 999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_999 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 999) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_999 : oddCount 999 12 = 6 ∧ acceleratedOrbit 12 999 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_999 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 999) = 3 ^ 6 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_999.1, data_12_999.2]

/-- Complete interval computation for depth 12, residue 1000. -/
theorem bounds_12_1000 : exactInterval 12 1000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1000 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1000) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1000 : oddCount 1000 12 = 6 ∧ acceleratedOrbit 12 1000 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1000 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1000) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1000.1, data_12_1000.2]

/-- Complete interval computation for depth 12, residue 1001. -/
theorem bounds_12_1001 : exactInterval 12 1001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1001 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1001) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1001 : oddCount 1001 12 = 9 ∧ acceleratedOrbit 12 1001 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1001 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1001) = 3 ^ 9 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1001.1, data_12_1001.2]

/-- Complete interval computation for depth 12, residue 1002. -/
theorem bounds_12_1002 : exactInterval 12 1002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1002 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1002) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1002 : oddCount 1002 12 = 6 ∧ acceleratedOrbit 12 1002 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1002 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1002) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1002.1, data_12_1002.2]

/-- Complete interval computation for depth 12, residue 1003. -/
theorem bounds_12_1003 : exactInterval 12 1003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1003 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1003) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1003 : oddCount 1003 12 = 8 ∧ acceleratedOrbit 12 1003 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1003 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1003) = 3 ^ 8 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1003.1, data_12_1003.2]

/-- Complete interval computation for depth 12, residue 1004. -/
theorem bounds_12_1004 : exactInterval 12 1004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1004 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1004) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1004 : oddCount 1004 12 = 8 ∧ acceleratedOrbit 12 1004 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1004 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1004) = 3 ^ 8 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1004.1, data_12_1004.2]

/-- Complete interval computation for depth 12, residue 1005. -/
theorem bounds_12_1005 : exactInterval 12 1005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1005 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1005) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1005 : oddCount 1005 12 = 8 ∧ acceleratedOrbit 12 1005 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1005 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1005) = 3 ^ 8 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1005.1, data_12_1005.2]

/-- Complete interval computation for depth 12, residue 1006. -/
theorem bounds_12_1006 : exactInterval 12 1006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1006 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1006) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1006 : oddCount 1006 12 = 8 ∧ acceleratedOrbit 12 1006 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1006 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1006) = 3 ^ 8 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1006.1, data_12_1006.2]

/-- Complete interval computation for depth 12, residue 1007. -/
theorem bounds_12_1007 : exactInterval 12 1007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1007 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1007) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1007 : oddCount 1007 12 = 8 ∧ acceleratedOrbit 12 1007 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1007 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1007) = 3 ^ 8 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1007.1, data_12_1007.2]

/-- Complete interval computation for depth 12, residue 1008. -/
theorem bounds_12_1008 : exactInterval 12 1008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1008 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1008) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1008 : oddCount 1008 12 = 6 ∧ acceleratedOrbit 12 1008 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1008 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1008) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1008.1, data_12_1008.2]

/-- Complete interval computation for depth 12, residue 1009. -/
theorem bounds_12_1009 : exactInterval 12 1009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1009 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1009) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1009 : oddCount 1009 12 = 6 ∧ acceleratedOrbit 12 1009 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1009 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1009) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1009.1, data_12_1009.2]

/-- Complete interval computation for depth 12, residue 1010. -/
theorem bounds_12_1010 : exactInterval 12 1010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1010 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1010) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1010 : oddCount 1010 12 = 7 ∧ acceleratedOrbit 12 1010 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1010 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1010) = 3 ^ 7 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1010.1, data_12_1010.2]

/-- Complete interval computation for depth 12, residue 1011. -/
theorem bounds_12_1011 : exactInterval 12 1011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1011 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1011) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1011 : oddCount 1011 12 = 7 ∧ acceleratedOrbit 12 1011 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1011 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1011) = 3 ^ 7 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1011.1, data_12_1011.2]

/-- Complete interval computation for depth 12, residue 1012. -/
theorem bounds_12_1012 : exactInterval 12 1012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1012 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1012) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1012 : oddCount 1012 12 = 6 ∧ acceleratedOrbit 12 1012 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1012 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1012) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1012.1, data_12_1012.2]

end Collatz.Research.StoppingAtlas.Batch0266
