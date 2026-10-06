import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0306

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9994. -/
theorem bounds_15_9994 : exactInterval 15 9994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9994 : oddCount 9994 15 = 9 ∧ acceleratedOrbit 15 9994 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9994) = 3 ^ 9 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9994.1, data_15_9994.2]

/-- Complete interval computation for depth 15, residue 9995. -/
theorem bounds_15_9995 : exactInterval 15 9995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9995 : oddCount 9995 15 = 9 ∧ acceleratedOrbit 15 9995 = 6007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9995) = 3 ^ 9 * m + 6007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9995.1, data_15_9995.2]

/-- Complete interval computation for depth 15, residue 9996. -/
theorem bounds_15_9996 : exactInterval 15 9996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9996 : oddCount 9996 15 = 9 ∧ acceleratedOrbit 15 9996 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9996) = 3 ^ 9 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9996.1, data_15_9996.2]

/-- Complete interval computation for depth 15, residue 9997. -/
theorem bounds_15_9997 : exactInterval 15 9997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9997 : oddCount 9997 15 = 9 ∧ acceleratedOrbit 15 9997 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9997) = 3 ^ 9 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9997.1, data_15_9997.2]

/-- Complete interval computation for depth 15, residue 9998. -/
theorem bounds_15_9998 : exactInterval 15 9998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9998 : oddCount 9998 15 = 7 ∧ acceleratedOrbit 15 9998 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9998) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9998.1, data_15_9998.2]

/-- Complete interval computation for depth 15, residue 9999. -/
theorem bounds_15_9999 : exactInterval 15 9999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9999 : oddCount 9999 15 = 7 ∧ acceleratedOrbit 15 9999 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9999) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9999.1, data_15_9999.2]

/-- Complete interval computation for depth 15, residue 10000. -/
theorem bounds_15_10000 : exactInterval 15 10000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10000 : oddCount 10000 15 = 4 ∧ acceleratedOrbit 15 10000 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10000) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10000.1, data_15_10000.2]

/-- Complete interval computation for depth 15, residue 10001. -/
theorem bounds_15_10001 : exactInterval 15 10001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10001 : oddCount 10001 15 = 9 ∧ acceleratedOrbit 15 10001 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10001) = 3 ^ 9 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10001.1, data_15_10001.2]

/-- Complete interval computation for depth 15, residue 10002. -/
theorem bounds_15_10002 : exactInterval 15 10002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10002 : oddCount 10002 15 = 9 ∧ acceleratedOrbit 15 10002 = 6011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10002) = 3 ^ 9 * m + 6011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10002.1, data_15_10002.2]

/-- Complete interval computation for depth 15, residue 10003. -/
theorem bounds_15_10003 : exactInterval 15 10003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10003 : oddCount 10003 15 = 9 ∧ acceleratedOrbit 15 10003 = 6011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10003) = 3 ^ 9 * m + 6011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10003.1, data_15_10003.2]

/-- Complete interval computation for depth 15, residue 10004. -/
theorem bounds_15_10004 : exactInterval 15 10004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10004 : oddCount 10004 15 = 4 ∧ acceleratedOrbit 15 10004 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10004) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10004.1, data_15_10004.2]

/-- Complete interval computation for depth 15, residue 10005. -/
theorem bounds_15_10005 : exactInterval 15 10005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10005 : oddCount 10005 15 = 4 ∧ acceleratedOrbit 15 10005 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10005) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10005.1, data_15_10005.2]

/-- Complete interval computation for depth 15, residue 10006. -/
theorem bounds_15_10006 : exactInterval 15 10006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10006 : oddCount 10006 15 = 9 ∧ acceleratedOrbit 15 10006 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10006) = 3 ^ 9 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10006.1, data_15_10006.2]

/-- Complete interval computation for depth 15, residue 10007. -/
theorem bounds_15_10007 : exactInterval 15 10007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10007 : oddCount 10007 15 = 9 ∧ acceleratedOrbit 15 10007 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10007) = 3 ^ 9 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10007.1, data_15_10007.2]

/-- Complete interval computation for depth 15, residue 10008. -/
theorem bounds_15_10008 : exactInterval 15 10008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10008 : oddCount 10008 15 = 4 ∧ acceleratedOrbit 15 10008 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10008) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10008.1, data_15_10008.2]

/-- Complete interval computation for depth 15, residue 10009. -/
theorem bounds_15_10009 : exactInterval 15 10009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10009 : oddCount 10009 15 = 11 ∧ acceleratedOrbit 15 10009 = 54128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10009) = 3 ^ 11 * m + 54128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10009.1, data_15_10009.2]

/-- Complete interval computation for depth 15, residue 10010. -/
theorem bounds_15_10010 : exactInterval 15 10010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10010 : oddCount 10010 15 = 4 ∧ acceleratedOrbit 15 10010 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10010) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10010.1, data_15_10010.2]

/-- Complete interval computation for depth 15, residue 10011. -/
theorem bounds_15_10011 : exactInterval 15 10011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10011 : oddCount 10011 15 = 13 ∧ acceleratedOrbit 15 10011 = 487154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10011) = 3 ^ 13 * m + 487154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10011.1, data_15_10011.2]

/-- Complete interval computation for depth 15, residue 10012. -/
theorem bounds_15_10012 : exactInterval 15 10012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10012 : oddCount 10012 15 = 9 ∧ acceleratedOrbit 15 10012 = 6020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10012) = 3 ^ 9 * m + 6020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10012.1, data_15_10012.2]

/-- Complete interval computation for depth 15, residue 10013. -/
theorem bounds_15_10013 : exactInterval 15 10013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10013 : oddCount 10013 15 = 9 ∧ acceleratedOrbit 15 10013 = 6020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10013) = 3 ^ 9 * m + 6020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10013.1, data_15_10013.2]

/-- Complete interval computation for depth 15, residue 10014. -/
theorem bounds_15_10014 : exactInterval 15 10014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10014 : oddCount 10014 15 = 9 ∧ acceleratedOrbit 15 10014 = 6020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10014) = 3 ^ 9 * m + 6020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10014.1, data_15_10014.2]

/-- Complete interval computation for depth 15, residue 10015. -/
theorem bounds_15_10015 : exactInterval 15 10015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10015 : oddCount 10015 15 = 8 ∧ acceleratedOrbit 15 10015 = 2006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10015) = 3 ^ 8 * m + 2006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10015.1, data_15_10015.2]

/-- Complete interval computation for depth 15, residue 10016. -/
theorem bounds_15_10016 : exactInterval 15 10016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10016 : oddCount 10016 15 = 7 ∧ acceleratedOrbit 15 10016 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10016) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10016.1, data_15_10016.2]

/-- Complete interval computation for depth 15, residue 10017. -/
theorem bounds_15_10017 : exactInterval 15 10017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10017 : oddCount 10017 15 = 6 ∧ acceleratedOrbit 15 10017 = 223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10017) = 3 ^ 6 * m + 223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10017.1, data_15_10017.2]

/-- Complete interval computation for depth 15, residue 10018. -/
theorem bounds_15_10018 : exactInterval 15 10018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10018 : oddCount 10018 15 = 7 ∧ acceleratedOrbit 15 10018 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10018) = 3 ^ 7 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10018.1, data_15_10018.2]

/-- Complete interval computation for depth 15, residue 10019. -/
theorem bounds_15_10019 : exactInterval 15 10019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10019 : oddCount 10019 15 = 7 ∧ acceleratedOrbit 15 10019 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10019) = 3 ^ 7 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10019.1, data_15_10019.2]

/-- Complete interval computation for depth 15, residue 10020. -/
theorem bounds_15_10020 : exactInterval 15 10020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10020 : oddCount 10020 15 = 7 ∧ acceleratedOrbit 15 10020 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10020) = 3 ^ 7 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10020.1, data_15_10020.2]

/-- Complete interval computation for depth 15, residue 10021. -/
theorem bounds_15_10021 : exactInterval 15 10021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10021 : oddCount 10021 15 = 7 ∧ acceleratedOrbit 15 10021 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10021) = 3 ^ 7 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10021.1, data_15_10021.2]

/-- Complete interval computation for depth 15, residue 10022. -/
theorem bounds_15_10022 : exactInterval 15 10022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10022 : oddCount 10022 15 = 7 ∧ acceleratedOrbit 15 10022 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10022) = 3 ^ 7 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10022.1, data_15_10022.2]

/-- Complete interval computation for depth 15, residue 10023. -/
theorem bounds_15_10023 : exactInterval 15 10023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10023 : oddCount 10023 15 = 9 ∧ acceleratedOrbit 15 10023 = 6022 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10023) = 3 ^ 9 * m + 6022 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10023.1, data_15_10023.2]

/-- Complete interval computation for depth 15, residue 10024. -/
theorem bounds_15_10024 : exactInterval 15 10024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10024 : oddCount 10024 15 = 7 ∧ acceleratedOrbit 15 10024 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10024) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10024.1, data_15_10024.2]

/-- Complete interval computation for depth 15, residue 10025. -/
theorem bounds_15_10025 : exactInterval 15 10025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10025 : oddCount 10025 15 = 8 ∧ acceleratedOrbit 15 10025 = 2008 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10025) = 3 ^ 8 * m + 2008 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10025.1, data_15_10025.2]

/-- Complete interval computation for depth 15, residue 10026. -/
theorem bounds_15_10026 : exactInterval 15 10026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10026 : oddCount 10026 15 = 7 ∧ acceleratedOrbit 15 10026 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10026) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10026.1, data_15_10026.2]

end Collatz.Research.PassageAtlas.Batch0306
