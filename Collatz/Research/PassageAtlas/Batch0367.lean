import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0367

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11993. -/
theorem bounds_15_11993 : exactInterval 15 11993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11993 : oddCount 11993 15 = 5 ∧ acceleratedOrbit 15 11993 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11993) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11993.1, data_15_11993.2]

/-- Complete interval computation for depth 15, residue 11994. -/
theorem bounds_15_11994 : exactInterval 15 11994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11994 : oddCount 11994 15 = 5 ∧ acceleratedOrbit 15 11994 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11994) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11994.1, data_15_11994.2]

/-- Complete interval computation for depth 15, residue 11995. -/
theorem bounds_15_11995 : exactInterval 15 11995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11995 : oddCount 11995 15 = 10 ∧ acceleratedOrbit 15 11995 = 21620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11995) = 3 ^ 10 * m + 21620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11995.1, data_15_11995.2]

/-- Complete interval computation for depth 15, residue 11996. -/
theorem bounds_15_11996 : exactInterval 15 11996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11996 : oddCount 11996 15 = 5 ∧ acceleratedOrbit 15 11996 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11996) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11996.1, data_15_11996.2]

/-- Complete interval computation for depth 15, residue 11997. -/
theorem bounds_15_11997 : exactInterval 15 11997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11997 : oddCount 11997 15 = 5 ∧ acceleratedOrbit 15 11997 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11997) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11997.1, data_15_11997.2]

/-- Complete interval computation for depth 15, residue 11998. -/
theorem bounds_15_11998 : exactInterval 15 11998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11998 : oddCount 11998 15 = 11 ∧ acceleratedOrbit 15 11998 = 64880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11998) = 3 ^ 11 * m + 64880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11998.1, data_15_11998.2]

/-- Complete interval computation for depth 15, residue 11999. -/
theorem bounds_15_11999 : exactInterval 15 11999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11999 : oddCount 11999 15 = 11 ∧ acceleratedOrbit 15 11999 = 64880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11999) = 3 ^ 11 * m + 64880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11999.1, data_15_11999.2]

/-- Complete interval computation for depth 15, residue 12000. -/
theorem bounds_15_12000 : exactInterval 15 12000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12000 : oddCount 12000 15 = 6 ∧ acceleratedOrbit 15 12000 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12000) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12000.1, data_15_12000.2]

/-- Complete interval computation for depth 15, residue 12001. -/
theorem bounds_15_12001 : exactInterval 15 12001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12001 : oddCount 12001 15 = 9 ∧ acceleratedOrbit 15 12001 = 7211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12001) = 3 ^ 9 * m + 7211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12001.1, data_15_12001.2]

/-- Complete interval computation for depth 15, residue 12002. -/
theorem bounds_15_12002 : exactInterval 15 12002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12002 : oddCount 12002 15 = 6 ∧ acceleratedOrbit 15 12002 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12002) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12002.1, data_15_12002.2]

/-- Complete interval computation for depth 15, residue 12003. -/
theorem bounds_15_12003 : exactInterval 15 12003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12003 : oddCount 12003 15 = 6 ∧ acceleratedOrbit 15 12003 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12003) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12003.1, data_15_12003.2]

/-- Complete interval computation for depth 15, residue 12004. -/
theorem bounds_15_12004 : exactInterval 15 12004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12004 : oddCount 12004 15 = 7 ∧ acceleratedOrbit 15 12004 = 803 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12004) = 3 ^ 7 * m + 803 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12004.1, data_15_12004.2]

/-- Complete interval computation for depth 15, residue 12005. -/
theorem bounds_15_12005 : exactInterval 15 12005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12005 : oddCount 12005 15 = 7 ∧ acceleratedOrbit 15 12005 = 803 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12005) = 3 ^ 7 * m + 803 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12005.1, data_15_12005.2]

/-- Complete interval computation for depth 15, residue 12006. -/
theorem bounds_15_12006 : exactInterval 15 12006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12006 : oddCount 12006 15 = 7 ∧ acceleratedOrbit 15 12006 = 803 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12006) = 3 ^ 7 * m + 803 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12006.1, data_15_12006.2]

/-- Complete interval computation for depth 15, residue 12007. -/
theorem bounds_15_12007 : exactInterval 15 12007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12007 : oddCount 12007 15 = 10 ∧ acceleratedOrbit 15 12007 = 21640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12007) = 3 ^ 10 * m + 21640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12007.1, data_15_12007.2]

/-- Complete interval computation for depth 15, residue 12008. -/
theorem bounds_15_12008 : exactInterval 15 12008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12008 : oddCount 12008 15 = 6 ∧ acceleratedOrbit 15 12008 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12008) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12008.1, data_15_12008.2]

/-- Complete interval computation for depth 15, residue 12009. -/
theorem bounds_15_12009 : exactInterval 15 12009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12009 : oddCount 12009 15 = 8 ∧ acceleratedOrbit 15 12009 = 2405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12009) = 3 ^ 8 * m + 2405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12009.1, data_15_12009.2]

/-- Complete interval computation for depth 15, residue 12010. -/
theorem bounds_15_12010 : exactInterval 15 12010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12010 : oddCount 12010 15 = 6 ∧ acceleratedOrbit 15 12010 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12010) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12010.1, data_15_12010.2]

/-- Complete interval computation for depth 15, residue 12011. -/
theorem bounds_15_12011 : exactInterval 15 12011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12011 : oddCount 12011 15 = 7 ∧ acceleratedOrbit 15 12011 = 802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12011) = 3 ^ 7 * m + 802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12011.1, data_15_12011.2]

/-- Complete interval computation for depth 15, residue 12012. -/
theorem bounds_15_12012 : exactInterval 15 12012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12012 : oddCount 12012 15 = 7 ∧ acceleratedOrbit 15 12012 = 803 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12012) = 3 ^ 7 * m + 803 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12012.1, data_15_12012.2]

/-- Complete interval computation for depth 15, residue 12013. -/
theorem bounds_15_12013 : exactInterval 15 12013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12013 : oddCount 12013 15 = 7 ∧ acceleratedOrbit 15 12013 = 803 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12013) = 3 ^ 7 * m + 803 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12013.1, data_15_12013.2]

/-- Complete interval computation for depth 15, residue 12014. -/
theorem bounds_15_12014 : exactInterval 15 12014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12014 : oddCount 12014 15 = 7 ∧ acceleratedOrbit 15 12014 = 803 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12014) = 3 ^ 7 * m + 803 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12014.1, data_15_12014.2]

/-- Complete interval computation for depth 15, residue 12015. -/
theorem bounds_15_12015 : exactInterval 15 12015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12015 : oddCount 12015 15 = 12 ∧ acceleratedOrbit 15 12015 = 194885 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12015) = 3 ^ 12 * m + 194885 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12015.1, data_15_12015.2]

/-- Complete interval computation for depth 15, residue 12016. -/
theorem bounds_15_12016 : exactInterval 15 12016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12016 : oddCount 12016 15 = 9 ∧ acceleratedOrbit 15 12016 = 7229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12016) = 3 ^ 9 * m + 7229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12016.1, data_15_12016.2]

/-- Complete interval computation for depth 15, residue 12017. -/
theorem bounds_15_12017 : exactInterval 15 12017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12017 : oddCount 12017 15 = 6 ∧ acceleratedOrbit 15 12017 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12017) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12017.1, data_15_12017.2]

/-- Complete interval computation for depth 15, residue 12018. -/
theorem bounds_15_12018 : exactInterval 15 12018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12018 : oddCount 12018 15 = 9 ∧ acceleratedOrbit 15 12018 = 7222 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12018) = 3 ^ 9 * m + 7222 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12018.1, data_15_12018.2]

/-- Complete interval computation for depth 15, residue 12019. -/
theorem bounds_15_12019 : exactInterval 15 12019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12019 : oddCount 12019 15 = 9 ∧ acceleratedOrbit 15 12019 = 7222 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12019) = 3 ^ 9 * m + 7222 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12019.1, data_15_12019.2]

/-- Complete interval computation for depth 15, residue 12020. -/
theorem bounds_15_12020 : exactInterval 15 12020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12020 : oddCount 12020 15 = 9 ∧ acceleratedOrbit 15 12020 = 7229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12020) = 3 ^ 9 * m + 7229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12020.1, data_15_12020.2]

/-- Complete interval computation for depth 15, residue 12021. -/
theorem bounds_15_12021 : exactInterval 15 12021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12021 : oddCount 12021 15 = 9 ∧ acceleratedOrbit 15 12021 = 7229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12021) = 3 ^ 9 * m + 7229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12021.1, data_15_12021.2]

/-- Complete interval computation for depth 15, residue 12022. -/
theorem bounds_15_12022 : exactInterval 15 12022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12022 : oddCount 12022 15 = 8 ∧ acceleratedOrbit 15 12022 = 2408 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12022) = 3 ^ 8 * m + 2408 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12022.1, data_15_12022.2]

/-- Complete interval computation for depth 15, residue 12023. -/
theorem bounds_15_12023 : exactInterval 15 12023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12023 : oddCount 12023 15 = 8 ∧ acceleratedOrbit 15 12023 = 2408 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12023) = 3 ^ 8 * m + 2408 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12023.1, data_15_12023.2]

/-- Complete interval computation for depth 15, residue 12024. -/
theorem bounds_15_12024 : exactInterval 15 12024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12024 : oddCount 12024 15 = 9 ∧ acceleratedOrbit 15 12024 = 7229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12024) = 3 ^ 9 * m + 7229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12024.1, data_15_12024.2]

end Collatz.Research.PassageAtlas.Batch0367
