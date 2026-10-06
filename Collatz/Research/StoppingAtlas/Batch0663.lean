import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0663

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3000. -/
theorem bounds_13_3000 : exactInterval 13 3000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3000 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3000) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3000 : oddCount 3000 13 = 6 ∧ acceleratedOrbit 13 3000 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3000 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3000) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3000.1, data_13_3000.2]

/-- Complete interval computation for depth 13, residue 3001. -/
theorem bounds_13_3001 : exactInterval 13 3001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3001 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3001) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3001 : oddCount 3001 13 = 7 ∧ acceleratedOrbit 13 3001 = 803 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3001 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3001) = 3 ^ 7 * m + 803 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3001.1, data_13_3001.2]

/-- Complete interval computation for depth 13, residue 3002. -/
theorem bounds_13_3002 : exactInterval 13 3002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3002 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3002) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3002 : oddCount 3002 13 = 6 ∧ acceleratedOrbit 13 3002 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3002 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3002) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3002.1, data_13_3002.2]

/-- Complete interval computation for depth 13, residue 3003. -/
theorem bounds_13_3003 : exactInterval 13 3003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3003 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3003) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3003 : oddCount 3003 13 = 7 ∧ acceleratedOrbit 13 3003 = 803 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3003 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3003) = 3 ^ 7 * m + 803 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3003.1, data_13_3003.2]

/-- Complete interval computation for depth 13, residue 3004. -/
theorem bounds_13_3004 : exactInterval 13 3004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3004 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3004) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3004 : oddCount 3004 13 = 9 ∧ acceleratedOrbit 13 3004 = 7229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3004 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3004) = 3 ^ 9 * m + 7229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3004.1, data_13_3004.2]

/-- Complete interval computation for depth 13, residue 3005. -/
theorem bounds_13_3005 : exactInterval 13 3005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3005 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3005) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3005 : oddCount 3005 13 = 9 ∧ acceleratedOrbit 13 3005 = 7229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3005 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3005) = 3 ^ 9 * m + 7229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3005.1, data_13_3005.2]

/-- Complete interval computation for depth 13, residue 3006. -/
theorem bounds_13_3006 : exactInterval 13 3006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3006 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3006) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3006 : oddCount 3006 13 = 9 ∧ acceleratedOrbit 13 3006 = 7229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3006 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3006) = 3 ^ 9 * m + 7229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3006.1, data_13_3006.2]

/-- Complete interval computation for depth 13, residue 3007. -/
theorem bounds_13_3007 : exactInterval 13 3007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3007 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3007) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3007 : oddCount 3007 13 = 10 ∧ acceleratedOrbit 13 3007 = 21683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3007 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3007) = 3 ^ 10 * m + 21683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3007.1, data_13_3007.2]

/-- Complete interval computation for depth 13, residue 3008. -/
theorem bounds_13_3008 : exactInterval 13 3008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3008 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3008) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3008 : oddCount 3008 13 = 5 ∧ acceleratedOrbit 13 3008 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3008 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3008) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3008.1, data_13_3008.2]

/-- Complete interval computation for depth 13, residue 3009. -/
theorem bounds_13_3009 : exactInterval 13 3009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3009 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3009) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3009 : oddCount 3009 13 = 7 ∧ acceleratedOrbit 13 3009 = 805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3009 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3009) = 3 ^ 7 * m + 805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3009.1, data_13_3009.2]

/-- Complete interval computation for depth 13, residue 3010. -/
theorem bounds_13_3010 : exactInterval 13 3010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3010 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3010) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3010 : oddCount 3010 13 = 7 ∧ acceleratedOrbit 13 3010 = 805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3010 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3010) = 3 ^ 7 * m + 805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3010.1, data_13_3010.2]

/-- Complete interval computation for depth 13, residue 3011. -/
theorem bounds_13_3011 : exactInterval 13 3011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3011 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3011) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3011 : oddCount 3011 13 = 7 ∧ acceleratedOrbit 13 3011 = 805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3011 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3011) = 3 ^ 7 * m + 805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3011.1, data_13_3011.2]

/-- Complete interval computation for depth 13, residue 3012. -/
theorem bounds_13_3012 : exactInterval 13 3012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3012 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3012) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3012 : oddCount 3012 13 = 3 ∧ acceleratedOrbit 13 3012 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3012 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3012) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3012.1, data_13_3012.2]

/-- Complete interval computation for depth 13, residue 3013. -/
theorem bounds_13_3013 : exactInterval 13 3013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3013 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3013) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3013 : oddCount 3013 13 = 3 ∧ acceleratedOrbit 13 3013 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3013 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3013) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3013.1, data_13_3013.2]

/-- Complete interval computation for depth 13, residue 3014. -/
theorem bounds_13_3014 : exactInterval 13 3014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3014 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3014) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3014 : oddCount 3014 13 = 3 ∧ acceleratedOrbit 13 3014 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3014 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3014) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3014.1, data_13_3014.2]

end Collatz.Research.StoppingAtlas.Batch0663
