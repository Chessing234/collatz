import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0672

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21987. -/
theorem bounds_15_21987 : exactInterval 15 21987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21987 : oddCount 21987 15 = 5 ∧ acceleratedOrbit 15 21987 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21987) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21987.1, data_15_21987.2]

/-- Complete interval computation for depth 15, residue 21988. -/
theorem bounds_15_21988 : exactInterval 15 21988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21988 : oddCount 21988 15 = 9 ∧ acceleratedOrbit 15 21988 = 13213 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21988) = 3 ^ 9 * m + 13213 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21988.1, data_15_21988.2]

/-- Complete interval computation for depth 15, residue 21989. -/
theorem bounds_15_21989 : exactInterval 15 21989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21989 : oddCount 21989 15 = 9 ∧ acceleratedOrbit 15 21989 = 13213 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21989) = 3 ^ 9 * m + 13213 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21989.1, data_15_21989.2]

/-- Complete interval computation for depth 15, residue 21990. -/
theorem bounds_15_21990 : exactInterval 15 21990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21990 : oddCount 21990 15 = 9 ∧ acceleratedOrbit 15 21990 = 13213 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21990) = 3 ^ 9 * m + 13213 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21990.1, data_15_21990.2]

/-- Complete interval computation for depth 15, residue 21991. -/
theorem bounds_15_21991 : exactInterval 15 21991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21991 : oddCount 21991 15 = 9 ∧ acceleratedOrbit 15 21991 = 13211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21991) = 3 ^ 9 * m + 13211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21991.1, data_15_21991.2]

/-- Complete interval computation for depth 15, residue 21992. -/
theorem bounds_15_21992 : exactInterval 15 21992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21992 : oddCount 21992 15 = 6 ∧ acceleratedOrbit 15 21992 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21992) = 3 ^ 6 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21992.1, data_15_21992.2]

/-- Complete interval computation for depth 15, residue 21993. -/
theorem bounds_15_21993 : exactInterval 15 21993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21993 : oddCount 21993 15 = 12 ∧ acceleratedOrbit 15 21993 = 356723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21993) = 3 ^ 12 * m + 356723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21993.1, data_15_21993.2]

/-- Complete interval computation for depth 15, residue 21994. -/
theorem bounds_15_21994 : exactInterval 15 21994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21994 : oddCount 21994 15 = 6 ∧ acceleratedOrbit 15 21994 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21994) = 3 ^ 6 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21994.1, data_15_21994.2]

/-- Complete interval computation for depth 15, residue 21995. -/
theorem bounds_15_21995 : exactInterval 15 21995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21995 : oddCount 21995 15 = 11 ∧ acceleratedOrbit 15 21995 = 118918 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21995) = 3 ^ 11 * m + 118918 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21995.1, data_15_21995.2]

/-- Complete interval computation for depth 15, residue 21996. -/
theorem bounds_15_21996 : exactInterval 15 21996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21996 : oddCount 21996 15 = 7 ∧ acceleratedOrbit 15 21996 = 1469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21996) = 3 ^ 7 * m + 1469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21996.1, data_15_21996.2]

/-- Complete interval computation for depth 15, residue 21997. -/
theorem bounds_15_21997 : exactInterval 15 21997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21997 : oddCount 21997 15 = 7 ∧ acceleratedOrbit 15 21997 = 1469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21997) = 3 ^ 7 * m + 1469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21997.1, data_15_21997.2]

/-- Complete interval computation for depth 15, residue 21998. -/
theorem bounds_15_21998 : exactInterval 15 21998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21998 : oddCount 21998 15 = 7 ∧ acceleratedOrbit 15 21998 = 1469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21998) = 3 ^ 7 * m + 1469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21998.1, data_15_21998.2]

/-- Complete interval computation for depth 15, residue 21999. -/
theorem bounds_15_21999 : exactInterval 15 21999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21999 : oddCount 21999 15 = 8 ∧ acceleratedOrbit 15 21999 = 4405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21999) = 3 ^ 8 * m + 4405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21999.1, data_15_21999.2]

/-- Complete interval computation for depth 15, residue 22000. -/
theorem bounds_15_22000 : exactInterval 15 22000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22000 : oddCount 22000 15 = 6 ∧ acceleratedOrbit 15 22000 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22000) = 3 ^ 6 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22000.1, data_15_22000.2]

/-- Complete interval computation for depth 15, residue 22001. -/
theorem bounds_15_22001 : exactInterval 15 22001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22001 : oddCount 22001 15 = 6 ∧ acceleratedOrbit 15 22001 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22001) = 3 ^ 6 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22001.1, data_15_22001.2]

/-- Complete interval computation for depth 15, residue 22002. -/
theorem bounds_15_22002 : exactInterval 15 22002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22002 : oddCount 22002 15 = 7 ∧ acceleratedOrbit 15 22002 = 1469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22002) = 3 ^ 7 * m + 1469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22002.1, data_15_22002.2]

/-- Complete interval computation for depth 15, residue 22003. -/
theorem bounds_15_22003 : exactInterval 15 22003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22003 : oddCount 22003 15 = 7 ∧ acceleratedOrbit 15 22003 = 1469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22003) = 3 ^ 7 * m + 1469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22003.1, data_15_22003.2]

/-- Complete interval computation for depth 15, residue 22004. -/
theorem bounds_15_22004 : exactInterval 15 22004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22004 : oddCount 22004 15 = 6 ∧ acceleratedOrbit 15 22004 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22004) = 3 ^ 6 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22004.1, data_15_22004.2]

/-- Complete interval computation for depth 15, residue 22005. -/
theorem bounds_15_22005 : exactInterval 15 22005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22005 : oddCount 22005 15 = 6 ∧ acceleratedOrbit 15 22005 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22005) = 3 ^ 6 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22005.1, data_15_22005.2]

/-- Complete interval computation for depth 15, residue 22006. -/
theorem bounds_15_22006 : exactInterval 15 22006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22006 : oddCount 22006 15 = 11 ∧ acceleratedOrbit 15 22006 = 118988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22006) = 3 ^ 11 * m + 118988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22006.1, data_15_22006.2]

/-- Complete interval computation for depth 15, residue 22007. -/
theorem bounds_15_22007 : exactInterval 15 22007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22007 : oddCount 22007 15 = 11 ∧ acceleratedOrbit 15 22007 = 118988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22007) = 3 ^ 11 * m + 118988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22007.1, data_15_22007.2]

/-- Complete interval computation for depth 15, residue 22008. -/
theorem bounds_15_22008 : exactInterval 15 22008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22008 : oddCount 22008 15 = 9 ∧ acceleratedOrbit 15 22008 = 13225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22008) = 3 ^ 9 * m + 13225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22008.1, data_15_22008.2]

/-- Complete interval computation for depth 15, residue 22009. -/
theorem bounds_15_22009 : exactInterval 15 22009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22009 : oddCount 22009 15 = 9 ∧ acceleratedOrbit 15 22009 = 13223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22009) = 3 ^ 9 * m + 13223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22009.1, data_15_22009.2]

/-- Complete interval computation for depth 15, residue 22010. -/
theorem bounds_15_22010 : exactInterval 15 22010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22010 : oddCount 22010 15 = 9 ∧ acceleratedOrbit 15 22010 = 13225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22010) = 3 ^ 9 * m + 13225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22010.1, data_15_22010.2]

/-- Complete interval computation for depth 15, residue 22011. -/
theorem bounds_15_22011 : exactInterval 15 22011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22011 : oddCount 22011 15 = 9 ∧ acceleratedOrbit 15 22011 = 13223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22011) = 3 ^ 9 * m + 13223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22011.1, data_15_22011.2]

/-- Complete interval computation for depth 15, residue 22012. -/
theorem bounds_15_22012 : exactInterval 15 22012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22012 : oddCount 22012 15 = 9 ∧ acceleratedOrbit 15 22012 = 13225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22012) = 3 ^ 9 * m + 13225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22012.1, data_15_22012.2]

/-- Complete interval computation for depth 15, residue 22013. -/
theorem bounds_15_22013 : exactInterval 15 22013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22013 : oddCount 22013 15 = 9 ∧ acceleratedOrbit 15 22013 = 13225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22013) = 3 ^ 9 * m + 13225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22013.1, data_15_22013.2]

/-- Complete interval computation for depth 15, residue 22014. -/
theorem bounds_15_22014 : exactInterval 15 22014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22014 : oddCount 22014 15 = 10 ∧ acceleratedOrbit 15 22014 = 39674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22014) = 3 ^ 10 * m + 39674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22014.1, data_15_22014.2]

/-- Complete interval computation for depth 15, residue 22015. -/
theorem bounds_15_22015 : exactInterval 15 22015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22015 : oddCount 22015 15 = 10 ∧ acceleratedOrbit 15 22015 = 39674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22015) = 3 ^ 10 * m + 39674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22015.1, data_15_22015.2]

/-- Complete interval computation for depth 15, residue 22016. -/
theorem bounds_15_22016 : exactInterval 15 22016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22016 : oddCount 22016 15 = 4 ∧ acceleratedOrbit 15 22016 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22016) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22016.1, data_15_22016.2]

/-- Complete interval computation for depth 15, residue 22017. -/
theorem bounds_15_22017 : exactInterval 15 22017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22017 : oddCount 22017 15 = 9 ∧ acceleratedOrbit 15 22017 = 13229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22017) = 3 ^ 9 * m + 13229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22017.1, data_15_22017.2]

/-- Complete interval computation for depth 15, residue 22018. -/
theorem bounds_15_22018 : exactInterval 15 22018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22018 : oddCount 22018 15 = 7 ∧ acceleratedOrbit 15 22018 = 1471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22018) = 3 ^ 7 * m + 1471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22018.1, data_15_22018.2]

/-- Complete interval computation for depth 15, residue 22019. -/
theorem bounds_15_22019 : exactInterval 15 22019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22019 : oddCount 22019 15 = 7 ∧ acceleratedOrbit 15 22019 = 1471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22019) = 3 ^ 7 * m + 1471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22019.1, data_15_22019.2]

end Collatz.Research.PassageAtlas.Batch0672
