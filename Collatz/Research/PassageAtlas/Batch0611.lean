import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0611

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19988. -/
theorem bounds_15_19988 : exactInterval 15 19988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19988 : oddCount 19988 15 = 8 ∧ acceleratedOrbit 15 19988 = 4009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19988) = 3 ^ 8 * m + 4009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19988.1, data_15_19988.2]

/-- Complete interval computation for depth 15, residue 19989. -/
theorem bounds_15_19989 : exactInterval 15 19989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19989 : oddCount 19989 15 = 8 ∧ acceleratedOrbit 15 19989 = 4009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19989) = 3 ^ 8 * m + 4009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19989.1, data_15_19989.2]

/-- Complete interval computation for depth 15, residue 19990. -/
theorem bounds_15_19990 : exactInterval 15 19990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19990 : oddCount 19990 15 = 9 ∧ acceleratedOrbit 15 19990 = 12014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19990) = 3 ^ 9 * m + 12014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19990.1, data_15_19990.2]

/-- Complete interval computation for depth 15, residue 19991. -/
theorem bounds_15_19991 : exactInterval 15 19991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19991 : oddCount 19991 15 = 9 ∧ acceleratedOrbit 15 19991 = 12014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19991) = 3 ^ 9 * m + 12014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19991.1, data_15_19991.2]

/-- Complete interval computation for depth 15, residue 19992. -/
theorem bounds_15_19992 : exactInterval 15 19992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19992 : oddCount 19992 15 = 8 ∧ acceleratedOrbit 15 19992 = 4009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19992) = 3 ^ 8 * m + 4009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19992.1, data_15_19992.2]

/-- Complete interval computation for depth 15, residue 19993. -/
theorem bounds_15_19993 : exactInterval 15 19993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19993 : oddCount 19993 15 = 9 ∧ acceleratedOrbit 15 19993 = 12014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19993) = 3 ^ 9 * m + 12014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19993.1, data_15_19993.2]

/-- Complete interval computation for depth 15, residue 19994. -/
theorem bounds_15_19994 : exactInterval 15 19994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19994 : oddCount 19994 15 = 8 ∧ acceleratedOrbit 15 19994 = 4009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19994) = 3 ^ 8 * m + 4009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19994.1, data_15_19994.2]

/-- Complete interval computation for depth 15, residue 19995. -/
theorem bounds_15_19995 : exactInterval 15 19995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19995 : oddCount 19995 15 = 10 ∧ acceleratedOrbit 15 19995 = 36035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19995) = 3 ^ 10 * m + 36035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19995.1, data_15_19995.2]

/-- Complete interval computation for depth 15, residue 19996. -/
theorem bounds_15_19996 : exactInterval 15 19996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19996 : oddCount 19996 15 = 7 ∧ acceleratedOrbit 15 19996 = 1336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19996) = 3 ^ 7 * m + 1336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19996.1, data_15_19996.2]

/-- Complete interval computation for depth 15, residue 19997. -/
theorem bounds_15_19997 : exactInterval 15 19997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19997 : oddCount 19997 15 = 7 ∧ acceleratedOrbit 15 19997 = 1336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19997) = 3 ^ 7 * m + 1336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19997.1, data_15_19997.2]

/-- Complete interval computation for depth 15, residue 19998. -/
theorem bounds_15_19998 : exactInterval 15 19998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19998 : oddCount 19998 15 = 7 ∧ acceleratedOrbit 15 19998 = 1336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19998) = 3 ^ 7 * m + 1336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19998.1, data_15_19998.2]

/-- Complete interval computation for depth 15, residue 19999. -/
theorem bounds_15_19999 : exactInterval 15 19999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19999 : oddCount 19999 15 = 11 ∧ acceleratedOrbit 15 19999 = 108125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19999) = 3 ^ 11 * m + 108125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19999.1, data_15_19999.2]

/-- Complete interval computation for depth 15, residue 20000. -/
theorem bounds_15_20000 : exactInterval 15 20000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20000 : oddCount 20000 15 = 3 ∧ acceleratedOrbit 15 20000 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20000) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20000.1, data_15_20000.2]

/-- Complete interval computation for depth 15, residue 20001. -/
theorem bounds_15_20001 : exactInterval 15 20001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20001 : oddCount 20001 15 = 8 ∧ acceleratedOrbit 15 20001 = 4006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20001) = 3 ^ 8 * m + 4006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20001.1, data_15_20001.2]

/-- Complete interval computation for depth 15, residue 20002. -/
theorem bounds_15_20002 : exactInterval 15 20002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20002 : oddCount 20002 15 = 8 ∧ acceleratedOrbit 15 20002 = 4009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20002) = 3 ^ 8 * m + 4009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20002.1, data_15_20002.2]

/-- Complete interval computation for depth 15, residue 20003. -/
theorem bounds_15_20003 : exactInterval 15 20003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20003 : oddCount 20003 15 = 8 ∧ acceleratedOrbit 15 20003 = 4009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20003) = 3 ^ 8 * m + 4009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20003.1, data_15_20003.2]

/-- Complete interval computation for depth 15, residue 20004. -/
theorem bounds_15_20004 : exactInterval 15 20004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20004 : oddCount 20004 15 = 8 ∧ acceleratedOrbit 15 20004 = 4007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20004) = 3 ^ 8 * m + 4007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20004.1, data_15_20004.2]

/-- Complete interval computation for depth 15, residue 20005. -/
theorem bounds_15_20005 : exactInterval 15 20005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20005 : oddCount 20005 15 = 8 ∧ acceleratedOrbit 15 20005 = 4007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20005) = 3 ^ 8 * m + 4007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20005.1, data_15_20005.2]

/-- Complete interval computation for depth 15, residue 20006. -/
theorem bounds_15_20006 : exactInterval 15 20006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20006 : oddCount 20006 15 = 8 ∧ acceleratedOrbit 15 20006 = 4007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20006) = 3 ^ 8 * m + 4007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20006.1, data_15_20006.2]

/-- Complete interval computation for depth 15, residue 20007. -/
theorem bounds_15_20007 : exactInterval 15 20007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20007 : oddCount 20007 15 = 7 ∧ acceleratedOrbit 15 20007 = 1336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20007) = 3 ^ 7 * m + 1336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20007.1, data_15_20007.2]

/-- Complete interval computation for depth 15, residue 20008. -/
theorem bounds_15_20008 : exactInterval 15 20008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20008 : oddCount 20008 15 = 3 ∧ acceleratedOrbit 15 20008 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20008) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20008.1, data_15_20008.2]

/-- Complete interval computation for depth 15, residue 20009. -/
theorem bounds_15_20009 : exactInterval 15 20009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20009 : oddCount 20009 15 = 9 ∧ acceleratedOrbit 15 20009 = 12020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20009) = 3 ^ 9 * m + 12020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20009.1, data_15_20009.2]

/-- Complete interval computation for depth 15, residue 20010. -/
theorem bounds_15_20010 : exactInterval 15 20010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20010 : oddCount 20010 15 = 3 ∧ acceleratedOrbit 15 20010 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20010) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20010.1, data_15_20010.2]

/-- Complete interval computation for depth 15, residue 20011. -/
theorem bounds_15_20011 : exactInterval 15 20011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20011 : oddCount 20011 15 = 8 ∧ acceleratedOrbit 15 20011 = 4009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20011) = 3 ^ 8 * m + 4009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20011.1, data_15_20011.2]

/-- Complete interval computation for depth 15, residue 20012. -/
theorem bounds_15_20012 : exactInterval 15 20012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20012 : oddCount 20012 15 = 9 ∧ acceleratedOrbit 15 20012 = 12028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20012) = 3 ^ 9 * m + 12028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20012.1, data_15_20012.2]

/-- Complete interval computation for depth 15, residue 20013. -/
theorem bounds_15_20013 : exactInterval 15 20013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20013 : oddCount 20013 15 = 9 ∧ acceleratedOrbit 15 20013 = 12028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20013) = 3 ^ 9 * m + 12028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20013.1, data_15_20013.2]

/-- Complete interval computation for depth 15, residue 20014. -/
theorem bounds_15_20014 : exactInterval 15 20014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20014 : oddCount 20014 15 = 9 ∧ acceleratedOrbit 15 20014 = 12028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20014) = 3 ^ 9 * m + 12028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20014.1, data_15_20014.2]

/-- Complete interval computation for depth 15, residue 20015. -/
theorem bounds_15_20015 : exactInterval 15 20015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20015 : oddCount 20015 15 = 11 ∧ acceleratedOrbit 15 20015 = 108211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20015) = 3 ^ 11 * m + 108211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20015.1, data_15_20015.2]

/-- Complete interval computation for depth 15, residue 20016. -/
theorem bounds_15_20016 : exactInterval 15 20016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20016 : oddCount 20016 15 = 3 ∧ acceleratedOrbit 15 20016 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20016) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20016.1, data_15_20016.2]

/-- Complete interval computation for depth 15, residue 20017. -/
theorem bounds_15_20017 : exactInterval 15 20017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20017 : oddCount 20017 15 = 10 ∧ acceleratedOrbit 15 20017 = 36085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20017) = 3 ^ 10 * m + 36085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20017.1, data_15_20017.2]

/-- Complete interval computation for depth 15, residue 20018. -/
theorem bounds_15_20018 : exactInterval 15 20018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20018 : oddCount 20018 15 = 10 ∧ acceleratedOrbit 15 20018 = 36085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20018) = 3 ^ 10 * m + 36085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20018.1, data_15_20018.2]

/-- Complete interval computation for depth 15, residue 20019. -/
theorem bounds_15_20019 : exactInterval 15 20019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20019 : oddCount 20019 15 = 10 ∧ acceleratedOrbit 15 20019 = 36085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20019) = 3 ^ 10 * m + 36085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20019.1, data_15_20019.2]

/-- Complete interval computation for depth 15, residue 20020. -/
theorem bounds_15_20020 : exactInterval 15 20020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20020 : oddCount 20020 15 = 3 ∧ acceleratedOrbit 15 20020 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20020) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20020.1, data_15_20020.2]

end Collatz.Research.PassageAtlas.Batch0611
