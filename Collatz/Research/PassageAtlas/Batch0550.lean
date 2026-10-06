import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0550

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17989. -/
theorem bounds_15_17989 : exactInterval 15 17989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17989 : oddCount 17989 15 = 5 ∧ acceleratedOrbit 15 17989 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17989) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17989.1, data_15_17989.2]

/-- Complete interval computation for depth 15, residue 17990. -/
theorem bounds_15_17990 : exactInterval 15 17990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17990 : oddCount 17990 15 = 5 ∧ acceleratedOrbit 15 17990 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17990) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17990.1, data_15_17990.2]

/-- Complete interval computation for depth 15, residue 17991. -/
theorem bounds_15_17991 : exactInterval 15 17991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17991 : oddCount 17991 15 = 10 ∧ acceleratedOrbit 15 17991 = 32426 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17991) = 3 ^ 10 * m + 32426 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17991.1, data_15_17991.2]

/-- Complete interval computation for depth 15, residue 17992. -/
theorem bounds_15_17992 : exactInterval 15 17992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17992 : oddCount 17992 15 = 5 ∧ acceleratedOrbit 15 17992 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17992) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17992.1, data_15_17992.2]

/-- Complete interval computation for depth 15, residue 17993. -/
theorem bounds_15_17993 : exactInterval 15 17993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17993 : oddCount 17993 15 = 9 ∧ acceleratedOrbit 15 17993 = 10810 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17993) = 3 ^ 9 * m + 10810 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17993.1, data_15_17993.2]

/-- Complete interval computation for depth 15, residue 17994. -/
theorem bounds_15_17994 : exactInterval 15 17994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17994 : oddCount 17994 15 = 5 ∧ acceleratedOrbit 15 17994 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17994) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17994.1, data_15_17994.2]

/-- Complete interval computation for depth 15, residue 17995. -/
theorem bounds_15_17995 : exactInterval 15 17995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17995 : oddCount 17995 15 = 5 ∧ acceleratedOrbit 15 17995 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17995) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17995.1, data_15_17995.2]

/-- Complete interval computation for depth 15, residue 17996. -/
theorem bounds_15_17996 : exactInterval 15 17996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17996 : oddCount 17996 15 = 5 ∧ acceleratedOrbit 15 17996 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17996) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17996.1, data_15_17996.2]

/-- Complete interval computation for depth 15, residue 17997. -/
theorem bounds_15_17997 : exactInterval 15 17997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17997 : oddCount 17997 15 = 5 ∧ acceleratedOrbit 15 17997 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17997) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17997.1, data_15_17997.2]

/-- Complete interval computation for depth 15, residue 17998. -/
theorem bounds_15_17998 : exactInterval 15 17998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17998 : oddCount 17998 15 = 10 ∧ acceleratedOrbit 15 17998 = 32440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17998) = 3 ^ 10 * m + 32440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17998.1, data_15_17998.2]

/-- Complete interval computation for depth 15, residue 17999. -/
theorem bounds_15_17999 : exactInterval 15 17999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17999 : oddCount 17999 15 = 10 ∧ acceleratedOrbit 15 17999 = 32440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17999) = 3 ^ 10 * m + 32440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17999.1, data_15_17999.2]

/-- Complete interval computation for depth 15, residue 18000. -/
theorem bounds_15_18000 : exactInterval 15 18000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18000 : oddCount 18000 15 = 6 ∧ acceleratedOrbit 15 18000 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18000) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18000.1, data_15_18000.2]

/-- Complete interval computation for depth 15, residue 18001. -/
theorem bounds_15_18001 : exactInterval 15 18001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18001 : oddCount 18001 15 = 9 ∧ acceleratedOrbit 15 18001 = 10817 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18001) = 3 ^ 9 * m + 10817 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18001.1, data_15_18001.2]

/-- Complete interval computation for depth 15, residue 18002. -/
theorem bounds_15_18002 : exactInterval 15 18002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18002 : oddCount 18002 15 = 9 ∧ acceleratedOrbit 15 18002 = 10817 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18002) = 3 ^ 9 * m + 10817 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18002.1, data_15_18002.2]

/-- Complete interval computation for depth 15, residue 18003. -/
theorem bounds_15_18003 : exactInterval 15 18003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18003 : oddCount 18003 15 = 9 ∧ acceleratedOrbit 15 18003 = 10817 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18003) = 3 ^ 9 * m + 10817 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18003.1, data_15_18003.2]

/-- Complete interval computation for depth 15, residue 18004. -/
theorem bounds_15_18004 : exactInterval 15 18004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18004 : oddCount 18004 15 = 6 ∧ acceleratedOrbit 15 18004 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18004) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18004.1, data_15_18004.2]

/-- Complete interval computation for depth 15, residue 18005. -/
theorem bounds_15_18005 : exactInterval 15 18005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18005 : oddCount 18005 15 = 6 ∧ acceleratedOrbit 15 18005 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18005) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18005.1, data_15_18005.2]

/-- Complete interval computation for depth 15, residue 18006. -/
theorem bounds_15_18006 : exactInterval 15 18006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18006 : oddCount 18006 15 = 8 ∧ acceleratedOrbit 15 18006 = 3608 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18006) = 3 ^ 8 * m + 3608 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18006.1, data_15_18006.2]

/-- Complete interval computation for depth 15, residue 18007. -/
theorem bounds_15_18007 : exactInterval 15 18007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18007 : oddCount 18007 15 = 8 ∧ acceleratedOrbit 15 18007 = 3608 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18007) = 3 ^ 8 * m + 3608 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18007.1, data_15_18007.2]

/-- Complete interval computation for depth 15, residue 18008. -/
theorem bounds_15_18008 : exactInterval 15 18008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18008 : oddCount 18008 15 = 7 ∧ acceleratedOrbit 15 18008 = 1205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18008) = 3 ^ 7 * m + 1205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18008.1, data_15_18008.2]

/-- Complete interval computation for depth 15, residue 18009. -/
theorem bounds_15_18009 : exactInterval 15 18009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18009 : oddCount 18009 15 = 8 ∧ acceleratedOrbit 15 18009 = 3608 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18009) = 3 ^ 8 * m + 3608 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18009.1, data_15_18009.2]

/-- Complete interval computation for depth 15, residue 18010. -/
theorem bounds_15_18010 : exactInterval 15 18010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18010 : oddCount 18010 15 = 7 ∧ acceleratedOrbit 15 18010 = 1205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18010) = 3 ^ 7 * m + 1205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18010.1, data_15_18010.2]

/-- Complete interval computation for depth 15, residue 18011. -/
theorem bounds_15_18011 : exactInterval 15 18011 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18011) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18011 : oddCount 18011 15 = 9 ∧ acceleratedOrbit 15 18011 = 10820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18011) = 3 ^ 9 * m + 10820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18011.1, data_15_18011.2]

/-- Complete interval computation for depth 15, residue 18012. -/
theorem bounds_15_18012 : exactInterval 15 18012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18012 : oddCount 18012 15 = 7 ∧ acceleratedOrbit 15 18012 = 1205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18012) = 3 ^ 7 * m + 1205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18012.1, data_15_18012.2]

/-- Complete interval computation for depth 15, residue 18013. -/
theorem bounds_15_18013 : exactInterval 15 18013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18013 : oddCount 18013 15 = 7 ∧ acceleratedOrbit 15 18013 = 1205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18013) = 3 ^ 7 * m + 1205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18013.1, data_15_18013.2]

/-- Complete interval computation for depth 15, residue 18014. -/
theorem bounds_15_18014 : exactInterval 15 18014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18014 : oddCount 18014 15 = 8 ∧ acceleratedOrbit 15 18014 = 3608 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18014) = 3 ^ 8 * m + 3608 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18014.1, data_15_18014.2]

/-- Complete interval computation for depth 15, residue 18015. -/
theorem bounds_15_18015 : exactInterval 15 18015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18015 : oddCount 18015 15 = 8 ∧ acceleratedOrbit 15 18015 = 3608 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18015) = 3 ^ 8 * m + 3608 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18015.1, data_15_18015.2]

/-- Complete interval computation for depth 15, residue 18016. -/
theorem bounds_15_18016 : exactInterval 15 18016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18016 : oddCount 18016 15 = 6 ∧ acceleratedOrbit 15 18016 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18016) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18016.1, data_15_18016.2]

/-- Complete interval computation for depth 15, residue 18017. -/
theorem bounds_15_18017 : exactInterval 15 18017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18017 : oddCount 18017 15 = 6 ∧ acceleratedOrbit 15 18017 = 401 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18017) = 3 ^ 6 * m + 401 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18017.1, data_15_18017.2]

/-- Complete interval computation for depth 15, residue 18018. -/
theorem bounds_15_18018 : exactInterval 15 18018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18018 : oddCount 18018 15 = 7 ∧ acceleratedOrbit 15 18018 = 1205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18018) = 3 ^ 7 * m + 1205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18018.1, data_15_18018.2]

/-- Complete interval computation for depth 15, residue 18019. -/
theorem bounds_15_18019 : exactInterval 15 18019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18019 : oddCount 18019 15 = 7 ∧ acceleratedOrbit 15 18019 = 1205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18019) = 3 ^ 7 * m + 1205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18019.1, data_15_18019.2]

/-- Complete interval computation for depth 15, residue 18020. -/
theorem bounds_15_18020 : exactInterval 15 18020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18020 : oddCount 18020 15 = 7 ∧ acceleratedOrbit 15 18020 = 1205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18020) = 3 ^ 7 * m + 1205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18020.1, data_15_18020.2]

/-- Complete interval computation for depth 15, residue 18021. -/
theorem bounds_15_18021 : exactInterval 15 18021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18021 : oddCount 18021 15 = 7 ∧ acceleratedOrbit 15 18021 = 1205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18021) = 3 ^ 7 * m + 1205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18021.1, data_15_18021.2]

end Collatz.Research.PassageAtlas.Batch0550
