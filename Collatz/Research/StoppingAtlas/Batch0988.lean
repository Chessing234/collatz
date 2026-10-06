import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0988

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7992. -/
theorem bounds_13_7992 : exactInterval 13 7992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7992 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7992) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7992 : oddCount 7992 13 = 6 ∧ acceleratedOrbit 13 7992 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7992 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7992) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7992.1, data_13_7992.2]

/-- Complete interval computation for depth 13, residue 7993. -/
theorem bounds_13_7993 : exactInterval 13 7993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7993 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7993) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7993 : oddCount 7993 13 = 7 ∧ acceleratedOrbit 13 7993 = 2135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7993 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7993) = 3 ^ 7 * m + 2135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7993.1, data_13_7993.2]

/-- Complete interval computation for depth 13, residue 7994. -/
theorem bounds_13_7994 : exactInterval 13 7994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7994 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7994) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7994 : oddCount 7994 13 = 6 ∧ acceleratedOrbit 13 7994 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7994 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7994) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7994.1, data_13_7994.2]

/-- Complete interval computation for depth 13, residue 7995. -/
theorem bounds_13_7995 : exactInterval 13 7995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7995 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7995) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7995 : oddCount 7995 13 = 6 ∧ acceleratedOrbit 13 7995 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7995 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7995) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7995.1, data_13_7995.2]

/-- Complete interval computation for depth 13, residue 7996. -/
theorem bounds_13_7996 : exactInterval 13 7996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7996 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7996) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7996 : oddCount 7996 13 = 6 ∧ acceleratedOrbit 13 7996 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7996 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7996) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7996.1, data_13_7996.2]

/-- Complete interval computation for depth 13, residue 7997. -/
theorem bounds_13_7997 : exactInterval 13 7997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7997 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7997) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7997 : oddCount 7997 13 = 6 ∧ acceleratedOrbit 13 7997 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7997 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7997) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7997.1, data_13_7997.2]

/-- Complete interval computation for depth 13, residue 7998. -/
theorem bounds_13_7998 : exactInterval 13 7998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7998 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7998) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7998 : oddCount 7998 13 = 9 ∧ acceleratedOrbit 13 7998 = 19223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7998 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7998) = 3 ^ 9 * m + 19223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7998.1, data_13_7998.2]

/-- Complete interval computation for depth 13, residue 7999. -/
theorem bounds_13_7999 : exactInterval 13 7999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7999 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7999) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7999 : oddCount 7999 13 = 9 ∧ acceleratedOrbit 13 7999 = 19223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7999 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7999) = 3 ^ 9 * m + 19223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7999.1, data_13_7999.2]

/-- Complete interval computation for depth 13, residue 8000. -/
theorem bounds_13_8000 : exactInterval 13 8000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8000 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8000) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8000 : oddCount 8000 13 = 5 ∧ acceleratedOrbit 13 8000 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8000 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8000) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8000.1, data_13_8000.2]

/-- Complete interval computation for depth 13, residue 8001. -/
theorem bounds_13_8001 : exactInterval 13 8001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8001 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8001) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8001 : oddCount 8001 13 = 5 ∧ acceleratedOrbit 13 8001 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8001 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8001) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8001.1, data_13_8001.2]

/-- Complete interval computation for depth 13, residue 8002. -/
theorem bounds_13_8002 : exactInterval 13 8002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8002 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8002) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8002 : oddCount 8002 13 = 6 ∧ acceleratedOrbit 13 8002 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8002 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8002) = 3 ^ 6 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8002.1, data_13_8002.2]

/-- Complete interval computation for depth 13, residue 8003. -/
theorem bounds_13_8003 : exactInterval 13 8003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8003 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8003) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8003 : oddCount 8003 13 = 6 ∧ acceleratedOrbit 13 8003 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8003 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8003) = 3 ^ 6 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8003.1, data_13_8003.2]

/-- Complete interval computation for depth 13, residue 8004. -/
theorem bounds_13_8004 : exactInterval 13 8004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8004 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8004) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8004 : oddCount 8004 13 = 5 ∧ acceleratedOrbit 13 8004 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8004 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8004) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8004.1, data_13_8004.2]

/-- Complete interval computation for depth 13, residue 8005. -/
theorem bounds_13_8005 : exactInterval 13 8005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8005 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8005) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8005 : oddCount 8005 13 = 5 ∧ acceleratedOrbit 13 8005 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8005 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8005) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8005.1, data_13_8005.2]

/-- Complete interval computation for depth 13, residue 8006. -/
theorem bounds_13_8006 : exactInterval 13 8006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8006 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8006) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8006 : oddCount 8006 13 = 5 ∧ acceleratedOrbit 13 8006 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8006 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8006) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8006.1, data_13_8006.2]

end Collatz.Research.StoppingAtlas.Batch0988
