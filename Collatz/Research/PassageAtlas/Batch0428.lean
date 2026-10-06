import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0428

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13991. -/
theorem bounds_15_13991 : exactInterval 15 13991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13991 : oddCount 13991 15 = 10 ∧ acceleratedOrbit 15 13991 = 25217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13991) = 3 ^ 10 * m + 25217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13991.1, data_15_13991.2]

/-- Complete interval computation for depth 15, residue 13992. -/
theorem bounds_15_13992 : exactInterval 15 13992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13992 : oddCount 13992 15 = 5 ∧ acceleratedOrbit 15 13992 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13992) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13992.1, data_15_13992.2]

/-- Complete interval computation for depth 15, residue 13993. -/
theorem bounds_15_13993 : exactInterval 15 13993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13993 : oddCount 13993 15 = 10 ∧ acceleratedOrbit 15 13993 = 25219 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13993) = 3 ^ 10 * m + 25219 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13993.1, data_15_13993.2]

/-- Complete interval computation for depth 15, residue 13994. -/
theorem bounds_15_13994 : exactInterval 15 13994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13994 : oddCount 13994 15 = 5 ∧ acceleratedOrbit 15 13994 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13994) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13994.1, data_15_13994.2]

/-- Complete interval computation for depth 15, residue 13995. -/
theorem bounds_15_13995 : exactInterval 15 13995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13995 : oddCount 13995 15 = 8 ∧ acceleratedOrbit 15 13995 = 2803 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13995) = 3 ^ 8 * m + 2803 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13995.1, data_15_13995.2]

/-- Complete interval computation for depth 15, residue 13996. -/
theorem bounds_15_13996 : exactInterval 15 13996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13996 : oddCount 13996 15 = 9 ∧ acceleratedOrbit 15 13996 = 8414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13996) = 3 ^ 9 * m + 8414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13996.1, data_15_13996.2]

/-- Complete interval computation for depth 15, residue 13997. -/
theorem bounds_15_13997 : exactInterval 15 13997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13997 : oddCount 13997 15 = 9 ∧ acceleratedOrbit 15 13997 = 8414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13997) = 3 ^ 9 * m + 8414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13997.1, data_15_13997.2]

/-- Complete interval computation for depth 15, residue 13998. -/
theorem bounds_15_13998 : exactInterval 15 13998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13998 : oddCount 13998 15 = 9 ∧ acceleratedOrbit 15 13998 = 8414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13998) = 3 ^ 9 * m + 8414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13998.1, data_15_13998.2]

/-- Complete interval computation for depth 15, residue 13999. -/
theorem bounds_15_13999 : exactInterval 15 13999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13999 : oddCount 13999 15 = 10 ∧ acceleratedOrbit 15 13999 = 25231 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13999) = 3 ^ 10 * m + 25231 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13999.1, data_15_13999.2]

/-- Complete interval computation for depth 15, residue 14000. -/
theorem bounds_15_14000 : exactInterval 15 14000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14000 : oddCount 14000 15 = 5 ∧ acceleratedOrbit 15 14000 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14000) = 3 ^ 5 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14000.1, data_15_14000.2]

/-- Complete interval computation for depth 15, residue 14001. -/
theorem bounds_15_14001 : exactInterval 15 14001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14001 : oddCount 14001 15 = 5 ∧ acceleratedOrbit 15 14001 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14001) = 3 ^ 5 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14001.1, data_15_14001.2]

/-- Complete interval computation for depth 15, residue 14002. -/
theorem bounds_15_14002 : exactInterval 15 14002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14002 : oddCount 14002 15 = 5 ∧ acceleratedOrbit 15 14002 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14002) = 3 ^ 5 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14002.1, data_15_14002.2]

/-- Complete interval computation for depth 15, residue 14003. -/
theorem bounds_15_14003 : exactInterval 15 14003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14003 : oddCount 14003 15 = 5 ∧ acceleratedOrbit 15 14003 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14003) = 3 ^ 5 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14003.1, data_15_14003.2]

/-- Complete interval computation for depth 15, residue 14004. -/
theorem bounds_15_14004 : exactInterval 15 14004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14004 : oddCount 14004 15 = 5 ∧ acceleratedOrbit 15 14004 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14004) = 3 ^ 5 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14004.1, data_15_14004.2]

/-- Complete interval computation for depth 15, residue 14005. -/
theorem bounds_15_14005 : exactInterval 15 14005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14005 : oddCount 14005 15 = 5 ∧ acceleratedOrbit 15 14005 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14005) = 3 ^ 5 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14005.1, data_15_14005.2]

/-- Complete interval computation for depth 15, residue 14006. -/
theorem bounds_15_14006 : exactInterval 15 14006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14006 : oddCount 14006 15 = 7 ∧ acceleratedOrbit 15 14006 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14006) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14006.1, data_15_14006.2]

/-- Complete interval computation for depth 15, residue 14007. -/
theorem bounds_15_14007 : exactInterval 15 14007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14007 : oddCount 14007 15 = 7 ∧ acceleratedOrbit 15 14007 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14007) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14007.1, data_15_14007.2]

/-- Complete interval computation for depth 15, residue 14008. -/
theorem bounds_15_14008 : exactInterval 15 14008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14008 : oddCount 14008 15 = 5 ∧ acceleratedOrbit 15 14008 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14008) = 3 ^ 5 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14008.1, data_15_14008.2]

/-- Complete interval computation for depth 15, residue 14009. -/
theorem bounds_15_14009 : exactInterval 15 14009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14009 : oddCount 14009 15 = 8 ∧ acceleratedOrbit 15 14009 = 2807 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14009) = 3 ^ 8 * m + 2807 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14009.1, data_15_14009.2]

/-- Complete interval computation for depth 15, residue 14010. -/
theorem bounds_15_14010 : exactInterval 15 14010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14010 : oddCount 14010 15 = 5 ∧ acceleratedOrbit 15 14010 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14010) = 3 ^ 5 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14010.1, data_15_14010.2]

/-- Complete interval computation for depth 15, residue 14011. -/
theorem bounds_15_14011 : exactInterval 15 14011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14011 : oddCount 14011 15 = 8 ∧ acceleratedOrbit 15 14011 = 2807 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14011) = 3 ^ 8 * m + 2807 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14011.1, data_15_14011.2]

/-- Complete interval computation for depth 15, residue 14012. -/
theorem bounds_15_14012 : exactInterval 15 14012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14012 : oddCount 14012 15 = 9 ∧ acceleratedOrbit 15 14012 = 8423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14012) = 3 ^ 9 * m + 8423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14012.1, data_15_14012.2]

/-- Complete interval computation for depth 15, residue 14013. -/
theorem bounds_15_14013 : exactInterval 15 14013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14013 : oddCount 14013 15 = 9 ∧ acceleratedOrbit 15 14013 = 8423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14013) = 3 ^ 9 * m + 8423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14013.1, data_15_14013.2]

/-- Complete interval computation for depth 15, residue 14014. -/
theorem bounds_15_14014 : exactInterval 15 14014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14014 : oddCount 14014 15 = 9 ∧ acceleratedOrbit 15 14014 = 8423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14014) = 3 ^ 9 * m + 8423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14014.1, data_15_14014.2]

/-- Complete interval computation for depth 15, residue 14015. -/
theorem bounds_15_14015 : exactInterval 15 14015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14015 : oddCount 14015 15 = 10 ∧ acceleratedOrbit 15 14015 = 25258 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14015) = 3 ^ 10 * m + 25258 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14015.1, data_15_14015.2]

/-- Complete interval computation for depth 15, residue 14016. -/
theorem bounds_15_14016 : exactInterval 15 14016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14016 : oddCount 14016 15 = 6 ∧ acceleratedOrbit 15 14016 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14016) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14016.1, data_15_14016.2]

/-- Complete interval computation for depth 15, residue 14017. -/
theorem bounds_15_14017 : exactInterval 15 14017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14017 : oddCount 14017 15 = 5 ∧ acceleratedOrbit 15 14017 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14017) = 3 ^ 5 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14017.1, data_15_14017.2]

/-- Complete interval computation for depth 15, residue 14018. -/
theorem bounds_15_14018 : exactInterval 15 14018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14018 : oddCount 14018 15 = 11 ∧ acceleratedOrbit 15 14018 = 75815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14018) = 3 ^ 11 * m + 75815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14018.1, data_15_14018.2]

/-- Complete interval computation for depth 15, residue 14019. -/
theorem bounds_15_14019 : exactInterval 15 14019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14019 : oddCount 14019 15 = 11 ∧ acceleratedOrbit 15 14019 = 75815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14019) = 3 ^ 11 * m + 75815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14019.1, data_15_14019.2]

/-- Complete interval computation for depth 15, residue 14020. -/
theorem bounds_15_14020 : exactInterval 15 14020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14020 : oddCount 14020 15 = 6 ∧ acceleratedOrbit 15 14020 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14020) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14020.1, data_15_14020.2]

/-- Complete interval computation for depth 15, residue 14021. -/
theorem bounds_15_14021 : exactInterval 15 14021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14021 : oddCount 14021 15 = 6 ∧ acceleratedOrbit 15 14021 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14021) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14021.1, data_15_14021.2]

/-- Complete interval computation for depth 15, residue 14022. -/
theorem bounds_15_14022 : exactInterval 15 14022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14022 : oddCount 14022 15 = 6 ∧ acceleratedOrbit 15 14022 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14022) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14022.1, data_15_14022.2]

/-- Complete interval computation for depth 15, residue 14023. -/
theorem bounds_15_14023 : exactInterval 15 14023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14023 : oddCount 14023 15 = 5 ∧ acceleratedOrbit 15 14023 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14023) = 3 ^ 5 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14023.1, data_15_14023.2]

end Collatz.Research.PassageAtlas.Batch0428
