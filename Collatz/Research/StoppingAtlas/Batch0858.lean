import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0858

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5995. -/
theorem bounds_13_5995 : exactInterval 13 5995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5995 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5995) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5995 : oddCount 5995 13 = 8 ∧ acceleratedOrbit 13 5995 = 4805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5995 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5995) = 3 ^ 8 * m + 4805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5995.1, data_13_5995.2]

/-- Complete interval computation for depth 13, residue 5996. -/
theorem bounds_13_5996 : exactInterval 13 5996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5996 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5996) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5996 : oddCount 5996 13 = 5 ∧ acceleratedOrbit 13 5996 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5996 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5996) = 3 ^ 5 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5996.1, data_13_5996.2]

/-- Complete interval computation for depth 13, residue 5997. -/
theorem bounds_13_5997 : exactInterval 13 5997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5997 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5997) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5997 : oddCount 5997 13 = 5 ∧ acceleratedOrbit 13 5997 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5997 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5997) = 3 ^ 5 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5997.1, data_13_5997.2]

/-- Complete interval computation for depth 13, residue 5998. -/
theorem bounds_13_5998 : exactInterval 13 5998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5998 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5998) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5998 : oddCount 5998 13 = 5 ∧ acceleratedOrbit 13 5998 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5998 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5998) = 3 ^ 5 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5998.1, data_13_5998.2]

/-- Complete interval computation for depth 13, residue 5999. -/
theorem bounds_13_5999 : exactInterval 13 5999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5999 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5999) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5999 : oddCount 5999 13 = 10 ∧ acceleratedOrbit 13 5999 = 43253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5999 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5999) = 3 ^ 10 * m + 43253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5999.1, data_13_5999.2]

/-- Complete interval computation for depth 13, residue 6000. -/
theorem bounds_13_6000 : exactInterval 13 6000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6000 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6000) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6000 : oddCount 6000 13 = 5 ∧ acceleratedOrbit 13 6000 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6000 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6000) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6000.1, data_13_6000.2]

/-- Complete interval computation for depth 13, residue 6001. -/
theorem bounds_13_6001 : exactInterval 13 6001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6001 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6001) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6001 : oddCount 6001 13 = 5 ∧ acceleratedOrbit 13 6001 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6001 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6001) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6001.1, data_13_6001.2]

/-- Complete interval computation for depth 13, residue 6002. -/
theorem bounds_13_6002 : exactInterval 13 6002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6002 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6002) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6002 : oddCount 6002 13 = 6 ∧ acceleratedOrbit 13 6002 = 535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6002 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6002) = 3 ^ 6 * m + 535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6002.1, data_13_6002.2]

/-- Complete interval computation for depth 13, residue 6003. -/
theorem bounds_13_6003 : exactInterval 13 6003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6003 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6003) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6003 : oddCount 6003 13 = 6 ∧ acceleratedOrbit 13 6003 = 535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6003 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6003) = 3 ^ 6 * m + 535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6003.1, data_13_6003.2]

/-- Complete interval computation for depth 13, residue 6004. -/
theorem bounds_13_6004 : exactInterval 13 6004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6004 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6004) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6004 : oddCount 6004 13 = 5 ∧ acceleratedOrbit 13 6004 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6004 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6004) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6004.1, data_13_6004.2]

/-- Complete interval computation for depth 13, residue 6005. -/
theorem bounds_13_6005 : exactInterval 13 6005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6005 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6005) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6005 : oddCount 6005 13 = 5 ∧ acceleratedOrbit 13 6005 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6005 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6005) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6005.1, data_13_6005.2]

/-- Complete interval computation for depth 13, residue 6006. -/
theorem bounds_13_6006 : exactInterval 13 6006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6006 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6006) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6006 : oddCount 6006 13 = 6 ∧ acceleratedOrbit 13 6006 = 535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6006 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6006) = 3 ^ 6 * m + 535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6006.1, data_13_6006.2]

/-- Complete interval computation for depth 13, residue 6007. -/
theorem bounds_13_6007 : exactInterval 13 6007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6007 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6007) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6007 : oddCount 6007 13 = 6 ∧ acceleratedOrbit 13 6007 = 535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6007 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6007) = 3 ^ 6 * m + 535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6007.1, data_13_6007.2]

/-- Complete interval computation for depth 13, residue 6008. -/
theorem bounds_13_6008 : exactInterval 13 6008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6008 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6008) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6008 : oddCount 6008 13 = 8 ∧ acceleratedOrbit 13 6008 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6008 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6008) = 3 ^ 8 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6008.1, data_13_6008.2]

/-- Complete interval computation for depth 13, residue 6009. -/
theorem bounds_13_6009 : exactInterval 13 6009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6009 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6009) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6009 : oddCount 6009 13 = 9 ∧ acceleratedOrbit 13 6009 = 14444 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6009 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6009) = 3 ^ 9 * m + 14444 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6009.1, data_13_6009.2]

end Collatz.Research.StoppingAtlas.Batch0858
