import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0489

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15990. -/
theorem bounds_15_15990 : exactInterval 15 15990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15990 : oddCount 15990 15 = 6 ∧ acceleratedOrbit 15 15990 = 356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15990) = 3 ^ 6 * m + 356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15990.1, data_15_15990.2]

/-- Complete interval computation for depth 15, residue 15991. -/
theorem bounds_15_15991 : exactInterval 15 15991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15991 : oddCount 15991 15 = 6 ∧ acceleratedOrbit 15 15991 = 356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15991) = 3 ^ 6 * m + 356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15991.1, data_15_15991.2]

/-- Complete interval computation for depth 15, residue 15992. -/
theorem bounds_15_15992 : exactInterval 15 15992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15992 : oddCount 15992 15 = 6 ∧ acceleratedOrbit 15 15992 = 356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15992) = 3 ^ 6 * m + 356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15992.1, data_15_15992.2]

/-- Complete interval computation for depth 15, residue 15993. -/
theorem bounds_15_15993 : exactInterval 15 15993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15993 : oddCount 15993 15 = 10 ∧ acceleratedOrbit 15 15993 = 28826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15993) = 3 ^ 10 * m + 28826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15993.1, data_15_15993.2]

/-- Complete interval computation for depth 15, residue 15994. -/
theorem bounds_15_15994 : exactInterval 15 15994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15994 : oddCount 15994 15 = 6 ∧ acceleratedOrbit 15 15994 = 356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15994) = 3 ^ 6 * m + 356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15994.1, data_15_15994.2]

/-- Complete interval computation for depth 15, residue 15995. -/
theorem bounds_15_15995 : exactInterval 15 15995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15995 : oddCount 15995 15 = 6 ∧ acceleratedOrbit 15 15995 = 356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15995) = 3 ^ 6 * m + 356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15995.1, data_15_15995.2]

/-- Complete interval computation for depth 15, residue 15996. -/
theorem bounds_15_15996 : exactInterval 15 15996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15996 : oddCount 15996 15 = 10 ∧ acceleratedOrbit 15 15996 = 28835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15996) = 3 ^ 10 * m + 28835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15996.1, data_15_15996.2]

/-- Complete interval computation for depth 15, residue 15997. -/
theorem bounds_15_15997 : exactInterval 15 15997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15997 : oddCount 15997 15 = 10 ∧ acceleratedOrbit 15 15997 = 28835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15997) = 3 ^ 10 * m + 28835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15997.1, data_15_15997.2]

/-- Complete interval computation for depth 15, residue 15998. -/
theorem bounds_15_15998 : exactInterval 15 15998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15998 : oddCount 15998 15 = 10 ∧ acceleratedOrbit 15 15998 = 28835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15998) = 3 ^ 10 * m + 28835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15998.1, data_15_15998.2]

/-- Complete interval computation for depth 15, residue 15999. -/
theorem bounds_15_15999 : exactInterval 15 15999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15999 : oddCount 15999 15 = 13 ∧ acceleratedOrbit 15 15999 = 778481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15999) = 3 ^ 13 * m + 778481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15999.1, data_15_15999.2]

/-- Complete interval computation for depth 15, residue 16000. -/
theorem bounds_15_16000 : exactInterval 15 16000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16000 : oddCount 16000 15 = 5 ∧ acceleratedOrbit 15 16000 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16000) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16000.1, data_15_16000.2]

/-- Complete interval computation for depth 15, residue 16001. -/
theorem bounds_15_16001 : exactInterval 15 16001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16001 : oddCount 16001 15 = 9 ∧ acceleratedOrbit 15 16001 = 9614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16001) = 3 ^ 9 * m + 9614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16001.1, data_15_16001.2]

/-- Complete interval computation for depth 15, residue 16002. -/
theorem bounds_15_16002 : exactInterval 15 16002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16002 : oddCount 16002 15 = 5 ∧ acceleratedOrbit 15 16002 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16002) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16002.1, data_15_16002.2]

/-- Complete interval computation for depth 15, residue 16003. -/
theorem bounds_15_16003 : exactInterval 15 16003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16003 : oddCount 16003 15 = 5 ∧ acceleratedOrbit 15 16003 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16003) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16003.1, data_15_16003.2]

/-- Complete interval computation for depth 15, residue 16004. -/
theorem bounds_15_16004 : exactInterval 15 16004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16004 : oddCount 16004 15 = 7 ∧ acceleratedOrbit 15 16004 = 1070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16004) = 3 ^ 7 * m + 1070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16004.1, data_15_16004.2]

/-- Complete interval computation for depth 15, residue 16005. -/
theorem bounds_15_16005 : exactInterval 15 16005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16005 : oddCount 16005 15 = 7 ∧ acceleratedOrbit 15 16005 = 1070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16005) = 3 ^ 7 * m + 1070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16005.1, data_15_16005.2]

/-- Complete interval computation for depth 15, residue 16006. -/
theorem bounds_15_16006 : exactInterval 15 16006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16006 : oddCount 16006 15 = 7 ∧ acceleratedOrbit 15 16006 = 1070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16006) = 3 ^ 7 * m + 1070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16006.1, data_15_16006.2]

/-- Complete interval computation for depth 15, residue 16007. -/
theorem bounds_15_16007 : exactInterval 15 16007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16007 : oddCount 16007 15 = 8 ∧ acceleratedOrbit 15 16007 = 3206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16007) = 3 ^ 8 * m + 3206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16007.1, data_15_16007.2]

/-- Complete interval computation for depth 15, residue 16008. -/
theorem bounds_15_16008 : exactInterval 15 16008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16008 : oddCount 16008 15 = 5 ∧ acceleratedOrbit 15 16008 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16008) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16008.1, data_15_16008.2]

/-- Complete interval computation for depth 15, residue 16009. -/
theorem bounds_15_16009 : exactInterval 15 16009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16009 : oddCount 16009 15 = 10 ∧ acceleratedOrbit 15 16009 = 28853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16009) = 3 ^ 10 * m + 28853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16009.1, data_15_16009.2]

/-- Complete interval computation for depth 15, residue 16010. -/
theorem bounds_15_16010 : exactInterval 15 16010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16010 : oddCount 16010 15 = 5 ∧ acceleratedOrbit 15 16010 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16010) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16010.1, data_15_16010.2]

/-- Complete interval computation for depth 15, residue 16011. -/
theorem bounds_15_16011 : exactInterval 15 16011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16011 : oddCount 16011 15 = 7 ∧ acceleratedOrbit 15 16011 = 1070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16011) = 3 ^ 7 * m + 1070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16011.1, data_15_16011.2]

/-- Complete interval computation for depth 15, residue 16012. -/
theorem bounds_15_16012 : exactInterval 15 16012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16012 : oddCount 16012 15 = 5 ∧ acceleratedOrbit 15 16012 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16012) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16012.1, data_15_16012.2]

/-- Complete interval computation for depth 15, residue 16013. -/
theorem bounds_15_16013 : exactInterval 15 16013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16013 : oddCount 16013 15 = 5 ∧ acceleratedOrbit 15 16013 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16013) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16013.1, data_15_16013.2]

/-- Complete interval computation for depth 15, residue 16014. -/
theorem bounds_15_16014 : exactInterval 15 16014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16014 : oddCount 16014 15 = 7 ∧ acceleratedOrbit 15 16014 = 1069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16014) = 3 ^ 7 * m + 1069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16014.1, data_15_16014.2]

/-- Complete interval computation for depth 15, residue 16015. -/
theorem bounds_15_16015 : exactInterval 15 16015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16015 : oddCount 16015 15 = 7 ∧ acceleratedOrbit 15 16015 = 1069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16015) = 3 ^ 7 * m + 1069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16015.1, data_15_16015.2]

/-- Complete interval computation for depth 15, residue 16016. -/
theorem bounds_15_16016 : exactInterval 15 16016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16016 : oddCount 16016 15 = 9 ∧ acceleratedOrbit 15 16016 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16016) = 3 ^ 9 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16016.1, data_15_16016.2]

/-- Complete interval computation for depth 15, residue 16017. -/
theorem bounds_15_16017 : exactInterval 15 16017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16017 : oddCount 16017 15 = 7 ∧ acceleratedOrbit 15 16017 = 1070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16017) = 3 ^ 7 * m + 1070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16017.1, data_15_16017.2]

/-- Complete interval computation for depth 15, residue 16018. -/
theorem bounds_15_16018 : exactInterval 15 16018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16018 : oddCount 16018 15 = 7 ∧ acceleratedOrbit 15 16018 = 1070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16018) = 3 ^ 7 * m + 1070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16018.1, data_15_16018.2]

/-- Complete interval computation for depth 15, residue 16019. -/
theorem bounds_15_16019 : exactInterval 15 16019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16019 : oddCount 16019 15 = 7 ∧ acceleratedOrbit 15 16019 = 1070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16019) = 3 ^ 7 * m + 1070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16019.1, data_15_16019.2]

/-- Complete interval computation for depth 15, residue 16020. -/
theorem bounds_15_16020 : exactInterval 15 16020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16020 : oddCount 16020 15 = 9 ∧ acceleratedOrbit 15 16020 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16020) = 3 ^ 9 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16020.1, data_15_16020.2]

/-- Complete interval computation for depth 15, residue 16021. -/
theorem bounds_15_16021 : exactInterval 15 16021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16021 : oddCount 16021 15 = 9 ∧ acceleratedOrbit 15 16021 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16021) = 3 ^ 9 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16021.1, data_15_16021.2]

/-- Complete interval computation for depth 15, residue 16022. -/
theorem bounds_15_16022 : exactInterval 15 16022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16022 : oddCount 16022 15 = 5 ∧ acceleratedOrbit 15 16022 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16022) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16022.1, data_15_16022.2]

end Collatz.Research.PassageAtlas.Batch0489
