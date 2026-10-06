import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0184

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5996. -/
theorem bounds_15_5996 : exactInterval 15 5996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5996 : oddCount 5996 15 = 6 ∧ acceleratedOrbit 15 5996 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5996) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5996.1, data_15_5996.2]

/-- Complete interval computation for depth 15, residue 5997. -/
theorem bounds_15_5997 : exactInterval 15 5997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5997 : oddCount 5997 15 = 6 ∧ acceleratedOrbit 15 5997 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5997) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5997.1, data_15_5997.2]

/-- Complete interval computation for depth 15, residue 5998. -/
theorem bounds_15_5998 : exactInterval 15 5998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5998 : oddCount 5998 15 = 6 ∧ acceleratedOrbit 15 5998 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5998) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5998.1, data_15_5998.2]

/-- Complete interval computation for depth 15, residue 5999. -/
theorem bounds_15_5999 : exactInterval 15 5999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5999 : oddCount 5999 15 = 11 ∧ acceleratedOrbit 15 5999 = 32440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5999) = 3 ^ 11 * m + 32440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5999.1, data_15_5999.2]

/-- Complete interval computation for depth 15, residue 6000. -/
theorem bounds_15_6000 : exactInterval 15 6000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6000 : oddCount 6000 15 = 7 ∧ acceleratedOrbit 15 6000 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6000) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6000.1, data_15_6000.2]

/-- Complete interval computation for depth 15, residue 6001. -/
theorem bounds_15_6001 : exactInterval 15 6001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6001 : oddCount 6001 15 = 7 ∧ acceleratedOrbit 15 6001 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6001) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6001.1, data_15_6001.2]

/-- Complete interval computation for depth 15, residue 6002. -/
theorem bounds_15_6002 : exactInterval 15 6002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6002 : oddCount 6002 15 = 8 ∧ acceleratedOrbit 15 6002 = 1205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6002) = 3 ^ 8 * m + 1205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6002.1, data_15_6002.2]

/-- Complete interval computation for depth 15, residue 6003. -/
theorem bounds_15_6003 : exactInterval 15 6003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6003 : oddCount 6003 15 = 8 ∧ acceleratedOrbit 15 6003 = 1205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6003) = 3 ^ 8 * m + 1205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6003.1, data_15_6003.2]

/-- Complete interval computation for depth 15, residue 6004. -/
theorem bounds_15_6004 : exactInterval 15 6004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6004 : oddCount 6004 15 = 7 ∧ acceleratedOrbit 15 6004 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6004) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6004.1, data_15_6004.2]

/-- Complete interval computation for depth 15, residue 6005. -/
theorem bounds_15_6005 : exactInterval 15 6005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6005 : oddCount 6005 15 = 7 ∧ acceleratedOrbit 15 6005 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6005) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6005.1, data_15_6005.2]

/-- Complete interval computation for depth 15, residue 6006. -/
theorem bounds_15_6006 : exactInterval 15 6006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6006 : oddCount 6006 15 = 8 ∧ acceleratedOrbit 15 6006 = 1205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6006) = 3 ^ 8 * m + 1205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6006.1, data_15_6006.2]

/-- Complete interval computation for depth 15, residue 6007. -/
theorem bounds_15_6007 : exactInterval 15 6007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6007 : oddCount 6007 15 = 8 ∧ acceleratedOrbit 15 6007 = 1205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6007) = 3 ^ 8 * m + 1205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6007.1, data_15_6007.2]

/-- Complete interval computation for depth 15, residue 6008. -/
theorem bounds_15_6008 : exactInterval 15 6008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6008 : oddCount 6008 15 = 10 ∧ acceleratedOrbit 15 6008 = 10844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6008) = 3 ^ 10 * m + 10844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6008.1, data_15_6008.2]

/-- Complete interval computation for depth 15, residue 6009. -/
theorem bounds_15_6009 : exactInterval 15 6009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6009 : oddCount 6009 15 = 9 ∧ acceleratedOrbit 15 6009 = 3611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6009) = 3 ^ 9 * m + 3611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6009.1, data_15_6009.2]

/-- Complete interval computation for depth 15, residue 6010. -/
theorem bounds_15_6010 : exactInterval 15 6010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6010 : oddCount 6010 15 = 10 ∧ acceleratedOrbit 15 6010 = 10844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6010) = 3 ^ 10 * m + 10844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6010.1, data_15_6010.2]

/-- Complete interval computation for depth 15, residue 6011. -/
theorem bounds_15_6011 : exactInterval 15 6011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6011 : oddCount 6011 15 = 8 ∧ acceleratedOrbit 15 6011 = 1204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6011) = 3 ^ 8 * m + 1204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6011.1, data_15_6011.2]

/-- Complete interval computation for depth 15, residue 6012. -/
theorem bounds_15_6012 : exactInterval 15 6012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6012 : oddCount 6012 15 = 10 ∧ acceleratedOrbit 15 6012 = 10844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6012) = 3 ^ 10 * m + 10844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6012.1, data_15_6012.2]

/-- Complete interval computation for depth 15, residue 6013. -/
theorem bounds_15_6013 : exactInterval 15 6013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6013 : oddCount 6013 15 = 10 ∧ acceleratedOrbit 15 6013 = 10844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6013) = 3 ^ 10 * m + 10844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6013.1, data_15_6013.2]

/-- Complete interval computation for depth 15, residue 6014. -/
theorem bounds_15_6014 : exactInterval 15 6014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6014 : oddCount 6014 15 = 11 ∧ acceleratedOrbit 15 6014 = 32525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6014) = 3 ^ 11 * m + 32525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6014.1, data_15_6014.2]

/-- Complete interval computation for depth 15, residue 6015. -/
theorem bounds_15_6015 : exactInterval 15 6015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6015 : oddCount 6015 15 = 11 ∧ acceleratedOrbit 15 6015 = 32525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6015) = 3 ^ 11 * m + 32525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6015.1, data_15_6015.2]

/-- Complete interval computation for depth 15, residue 6016. -/
theorem bounds_15_6016 : exactInterval 15 6016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6016 : oddCount 6016 15 = 6 ∧ acceleratedOrbit 15 6016 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6016) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6016.1, data_15_6016.2]

/-- Complete interval computation for depth 15, residue 6017. -/
theorem bounds_15_6017 : exactInterval 15 6017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6017 : oddCount 6017 15 = 10 ∧ acceleratedOrbit 15 6017 = 10853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6017) = 3 ^ 10 * m + 10853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6017.1, data_15_6017.2]

/-- Complete interval computation for depth 15, residue 6018. -/
theorem bounds_15_6018 : exactInterval 15 6018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6018 : oddCount 6018 15 = 8 ∧ acceleratedOrbit 15 6018 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6018) = 3 ^ 8 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6018.1, data_15_6018.2]

/-- Complete interval computation for depth 15, residue 6019. -/
theorem bounds_15_6019 : exactInterval 15 6019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6019 : oddCount 6019 15 = 8 ∧ acceleratedOrbit 15 6019 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6019) = 3 ^ 8 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6019.1, data_15_6019.2]

/-- Complete interval computation for depth 15, residue 6020. -/
theorem bounds_15_6020 : exactInterval 15 6020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6020 : oddCount 6020 15 = 8 ∧ acceleratedOrbit 15 6020 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6020) = 3 ^ 8 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6020.1, data_15_6020.2]

/-- Complete interval computation for depth 15, residue 6021. -/
theorem bounds_15_6021 : exactInterval 15 6021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6021 : oddCount 6021 15 = 8 ∧ acceleratedOrbit 15 6021 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6021) = 3 ^ 8 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6021.1, data_15_6021.2]

/-- Complete interval computation for depth 15, residue 6022. -/
theorem bounds_15_6022 : exactInterval 15 6022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6022 : oddCount 6022 15 = 8 ∧ acceleratedOrbit 15 6022 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6022) = 3 ^ 8 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6022.1, data_15_6022.2]

/-- Complete interval computation for depth 15, residue 6023. -/
theorem bounds_15_6023 : exactInterval 15 6023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6023 : oddCount 6023 15 = 8 ∧ acceleratedOrbit 15 6023 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6023) = 3 ^ 8 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6023.1, data_15_6023.2]

/-- Complete interval computation for depth 15, residue 6024. -/
theorem bounds_15_6024 : exactInterval 15 6024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6024 : oddCount 6024 15 = 3 ∧ acceleratedOrbit 15 6024 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6024) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6024.1, data_15_6024.2]

/-- Complete interval computation for depth 15, residue 6025. -/
theorem bounds_15_6025 : exactInterval 15 6025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6025 : oddCount 6025 15 = 8 ∧ acceleratedOrbit 15 6025 = 1207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6025) = 3 ^ 8 * m + 1207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6025.1, data_15_6025.2]

/-- Complete interval computation for depth 15, residue 6026. -/
theorem bounds_15_6026 : exactInterval 15 6026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6026 : oddCount 6026 15 = 3 ∧ acceleratedOrbit 15 6026 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6026) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6026.1, data_15_6026.2]

/-- Complete interval computation for depth 15, residue 6027. -/
theorem bounds_15_6027 : exactInterval 15 6027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6027 : oddCount 6027 15 = 10 ∧ acceleratedOrbit 15 6027 = 10867 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6027) = 3 ^ 10 * m + 10867 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6027.1, data_15_6027.2]

/-- Complete interval computation for depth 15, residue 6028. -/
theorem bounds_15_6028 : exactInterval 15 6028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6028 : oddCount 6028 15 = 3 ∧ acceleratedOrbit 15 6028 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6028) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6028.1, data_15_6028.2]

end Collatz.Research.PassageAtlas.Batch0184
