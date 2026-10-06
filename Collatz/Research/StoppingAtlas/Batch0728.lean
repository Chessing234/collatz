import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0728

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3998. -/
theorem bounds_13_3998 : exactInterval 13 3998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3998 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3998) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3998 : oddCount 3998 13 = 6 ∧ acceleratedOrbit 13 3998 = 356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3998 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3998) = 3 ^ 6 * m + 356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3998.1, data_13_3998.2]

/-- Complete interval computation for depth 13, residue 3999. -/
theorem bounds_13_3999 : exactInterval 13 3999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3999 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3999) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3999 : oddCount 3999 13 = 10 ∧ acceleratedOrbit 13 3999 = 28835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3999 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3999) = 3 ^ 10 * m + 28835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3999.1, data_13_3999.2]

/-- Complete interval computation for depth 13, residue 4000. -/
theorem bounds_13_4000 : exactInterval 13 4000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4000 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4000) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4000 : oddCount 4000 13 = 5 ∧ acceleratedOrbit 13 4000 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4000 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4000) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4000.1, data_13_4000.2]

/-- Complete interval computation for depth 13, residue 4001. -/
theorem bounds_13_4001 : exactInterval 13 4001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4001 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4001) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4001 : oddCount 4001 13 = 7 ∧ acceleratedOrbit 13 4001 = 1070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4001 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4001) = 3 ^ 7 * m + 1070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4001.1, data_13_4001.2]

/-- Complete interval computation for depth 13, residue 4002. -/
theorem bounds_13_4002 : exactInterval 13 4002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4002 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4002) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4002 : oddCount 4002 13 = 5 ∧ acceleratedOrbit 13 4002 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4002 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4002) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4002.1, data_13_4002.2]

/-- Complete interval computation for depth 13, residue 4003. -/
theorem bounds_13_4003 : exactInterval 13 4003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4003 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4003) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4003 : oddCount 4003 13 = 5 ∧ acceleratedOrbit 13 4003 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4003 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4003) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4003.1, data_13_4003.2]

/-- Complete interval computation for depth 13, residue 4004. -/
theorem bounds_13_4004 : exactInterval 13 4004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4004 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4004) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4004 : oddCount 4004 13 = 9 ∧ acceleratedOrbit 13 4004 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4004 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4004) = 3 ^ 9 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4004.1, data_13_4004.2]

/-- Complete interval computation for depth 13, residue 4005. -/
theorem bounds_13_4005 : exactInterval 13 4005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4005 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4005) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4005 : oddCount 4005 13 = 9 ∧ acceleratedOrbit 13 4005 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4005 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4005) = 3 ^ 9 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4005.1, data_13_4005.2]

/-- Complete interval computation for depth 13, residue 4006. -/
theorem bounds_13_4006 : exactInterval 13 4006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4006 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4006) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4006 : oddCount 4006 13 = 9 ∧ acceleratedOrbit 13 4006 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4006 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4006) = 3 ^ 9 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4006.1, data_13_4006.2]

/-- Complete interval computation for depth 13, residue 4007. -/
theorem bounds_13_4007 : exactInterval 13 4007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4007 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4007) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4007 : oddCount 4007 13 = 9 ∧ acceleratedOrbit 13 4007 = 9632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4007 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4007) = 3 ^ 9 * m + 9632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4007.1, data_13_4007.2]

/-- Complete interval computation for depth 13, residue 4008. -/
theorem bounds_13_4008 : exactInterval 13 4008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4008 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4008) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4008 : oddCount 4008 13 = 5 ∧ acceleratedOrbit 13 4008 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4008 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4008) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4008.1, data_13_4008.2]

/-- Complete interval computation for depth 13, residue 4009. -/
theorem bounds_13_4009 : exactInterval 13 4009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4009 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4009) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4009 : oddCount 4009 13 = 10 ∧ acceleratedOrbit 13 4009 = 28910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4009 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4009) = 3 ^ 10 * m + 28910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4009.1, data_13_4009.2]

/-- Complete interval computation for depth 13, residue 4010. -/
theorem bounds_13_4010 : exactInterval 13 4010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4010 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4010) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4010 : oddCount 4010 13 = 5 ∧ acceleratedOrbit 13 4010 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4010 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4010) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4010.1, data_13_4010.2]

/-- Complete interval computation for depth 13, residue 4011. -/
theorem bounds_13_4011 : exactInterval 13 4011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4011 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4011) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4011 : oddCount 4011 13 = 8 ∧ acceleratedOrbit 13 4011 = 3215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4011 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4011) = 3 ^ 8 * m + 3215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4011.1, data_13_4011.2]

/-- Complete interval computation for depth 13, residue 4012. -/
theorem bounds_13_4012 : exactInterval 13 4012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4012 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4012) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4012 : oddCount 4012 13 = 7 ∧ acceleratedOrbit 13 4012 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4012 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4012) = 3 ^ 7 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4012.1, data_13_4012.2]

/-- Complete interval computation for depth 13, residue 4013. -/
theorem bounds_13_4013 : exactInterval 13 4013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4013 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4013) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4013 : oddCount 4013 13 = 7 ∧ acceleratedOrbit 13 4013 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4013 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4013) = 3 ^ 7 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4013.1, data_13_4013.2]

end Collatz.Research.StoppingAtlas.Batch0728
