import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0793

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4997. -/
theorem bounds_13_4997 : exactInterval 13 4997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4997 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4997) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4997 : oddCount 4997 13 = 8 ∧ acceleratedOrbit 13 4997 = 4009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4997 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4997) = 3 ^ 8 * m + 4009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4997.1, data_13_4997.2]

/-- Complete interval computation for depth 13, residue 4998. -/
theorem bounds_13_4998 : exactInterval 13 4998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4998 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4998) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4998 : oddCount 4998 13 = 8 ∧ acceleratedOrbit 13 4998 = 4009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4998 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4998) = 3 ^ 8 * m + 4009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4998.1, data_13_4998.2]

/-- Complete interval computation for depth 13, residue 4999. -/
theorem bounds_13_4999 : exactInterval 13 4999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4999 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4999) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4999 : oddCount 4999 13 = 7 ∧ acceleratedOrbit 13 4999 = 1336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4999 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4999) = 3 ^ 7 * m + 1336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4999.1, data_13_4999.2]

/-- Complete interval computation for depth 13, residue 5000. -/
theorem bounds_13_5000 : exactInterval 13 5000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5000 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5000) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5000 : oddCount 5000 13 = 3 ∧ acceleratedOrbit 13 5000 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5000 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5000) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5000.1, data_13_5000.2]

/-- Complete interval computation for depth 13, residue 5001. -/
theorem bounds_13_5001 : exactInterval 13 5001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5001 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5001) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5001 : oddCount 5001 13 = 8 ∧ acceleratedOrbit 13 5001 = 4007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5001 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5001) = 3 ^ 8 * m + 4007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5001.1, data_13_5001.2]

/-- Complete interval computation for depth 13, residue 5002. -/
theorem bounds_13_5002 : exactInterval 13 5002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5002 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5002) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5002 : oddCount 5002 13 = 3 ∧ acceleratedOrbit 13 5002 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5002 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5002) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5002.1, data_13_5002.2]

/-- Complete interval computation for depth 13, residue 5003. -/
theorem bounds_13_5003 : exactInterval 13 5003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5003 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5003) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5003 : oddCount 5003 13 = 9 ∧ acceleratedOrbit 13 5003 = 12028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5003 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5003) = 3 ^ 9 * m + 12028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5003.1, data_13_5003.2]

/-- Complete interval computation for depth 13, residue 5004. -/
theorem bounds_13_5004 : exactInterval 13 5004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5004 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5004) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5004 : oddCount 5004 13 = 3 ∧ acceleratedOrbit 13 5004 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5004 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5004) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5004.1, data_13_5004.2]

/-- Complete interval computation for depth 13, residue 5005. -/
theorem bounds_13_5005 : exactInterval 13 5005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5005 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5005) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5005 : oddCount 5005 13 = 3 ∧ acceleratedOrbit 13 5005 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5005 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5005) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5005.1, data_13_5005.2]

/-- Complete interval computation for depth 13, residue 5006. -/
theorem bounds_13_5006 : exactInterval 13 5006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5006 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5006) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5006 : oddCount 5006 13 = 8 ∧ acceleratedOrbit 13 5006 = 4013 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5006 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5006) = 3 ^ 8 * m + 4013 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5006.1, data_13_5006.2]

/-- Complete interval computation for depth 13, residue 5007. -/
theorem bounds_13_5007 : exactInterval 13 5007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5007 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5007) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5007 : oddCount 5007 13 = 8 ∧ acceleratedOrbit 13 5007 = 4013 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5007 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5007) = 3 ^ 8 * m + 4013 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5007.1, data_13_5007.2]

/-- Complete interval computation for depth 13, residue 5008. -/
theorem bounds_13_5008 : exactInterval 13 5008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5008 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5008) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5008 : oddCount 5008 13 = 6 ∧ acceleratedOrbit 13 5008 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5008 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5008) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5008.1, data_13_5008.2]

/-- Complete interval computation for depth 13, residue 5009. -/
theorem bounds_13_5009 : exactInterval 13 5009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5009 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5009) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5009 : oddCount 5009 13 = 7 ∧ acceleratedOrbit 13 5009 = 1340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5009 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5009) = 3 ^ 7 * m + 1340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5009.1, data_13_5009.2]

/-- Complete interval computation for depth 13, residue 5010. -/
theorem bounds_13_5010 : exactInterval 13 5010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5010 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5010) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5010 : oddCount 5010 13 = 7 ∧ acceleratedOrbit 13 5010 = 1340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5010 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5010) = 3 ^ 7 * m + 1340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5010.1, data_13_5010.2]

/-- Complete interval computation for depth 13, residue 5011. -/
theorem bounds_13_5011 : exactInterval 13 5011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5011 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5011) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5011 : oddCount 5011 13 = 7 ∧ acceleratedOrbit 13 5011 = 1340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5011 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5011) = 3 ^ 7 * m + 1340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5011.1, data_13_5011.2]

end Collatz.Research.StoppingAtlas.Batch0793
