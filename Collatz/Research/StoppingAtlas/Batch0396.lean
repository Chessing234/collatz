import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0396

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2995. -/
theorem bounds_12_2995 : exactInterval 12 2995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2995 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2995) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2995 : oddCount 2995 12 = 5 ∧ acceleratedOrbit 12 2995 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2995 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2995) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2995.1, data_12_2995.2]

/-- Complete interval computation for depth 12, residue 2996. -/
theorem bounds_12_2996 : exactInterval 12 2996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2996 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2996) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2996 : oddCount 2996 12 = 5 ∧ acceleratedOrbit 12 2996 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2996 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2996) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2996.1, data_12_2996.2]

/-- Complete interval computation for depth 12, residue 2997. -/
theorem bounds_12_2997 : exactInterval 12 2997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2997 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2997) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2997 : oddCount 2997 12 = 5 ∧ acceleratedOrbit 12 2997 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2997 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2997) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2997.1, data_12_2997.2]

/-- Complete interval computation for depth 12, residue 2998. -/
theorem bounds_12_2998 : exactInterval 12 2998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2998 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2998) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2998 : oddCount 2998 12 = 5 ∧ acceleratedOrbit 12 2998 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2998 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2998) = 3 ^ 5 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2998.1, data_12_2998.2]

/-- Complete interval computation for depth 12, residue 2999. -/
theorem bounds_12_2999 : exactInterval 12 2999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2999 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2999) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2999 : oddCount 2999 12 = 5 ∧ acceleratedOrbit 12 2999 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2999 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2999) = 3 ^ 5 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2999.1, data_12_2999.2]

/-- Complete interval computation for depth 12, residue 3000. -/
theorem bounds_12_3000 : exactInterval 12 3000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3000 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3000) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3000 : oddCount 3000 12 = 5 ∧ acceleratedOrbit 12 3000 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3000 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3000) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3000.1, data_12_3000.2]

/-- Complete interval computation for depth 12, residue 3001. -/
theorem bounds_12_3001 : exactInterval 12 3001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3001 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3001) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3001 : oddCount 3001 12 = 6 ∧ acceleratedOrbit 12 3001 = 535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3001 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3001) = 3 ^ 6 * m + 535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3001.1, data_12_3001.2]

/-- Complete interval computation for depth 12, residue 3002. -/
theorem bounds_12_3002 : exactInterval 12 3002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3002 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3002) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3002 : oddCount 3002 12 = 5 ∧ acceleratedOrbit 12 3002 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3002 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3002) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3002.1, data_12_3002.2]

/-- Complete interval computation for depth 12, residue 3003. -/
theorem bounds_12_3003 : exactInterval 12 3003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3003 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3003) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3003 : oddCount 3003 12 = 6 ∧ acceleratedOrbit 12 3003 = 535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3003 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3003) = 3 ^ 6 * m + 535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3003.1, data_12_3003.2]

/-- Complete interval computation for depth 12, residue 3004. -/
theorem bounds_12_3004 : exactInterval 12 3004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3004 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3004) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3004 : oddCount 3004 12 = 8 ∧ acceleratedOrbit 12 3004 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3004 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3004) = 3 ^ 8 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3004.1, data_12_3004.2]

/-- Complete interval computation for depth 12, residue 3005. -/
theorem bounds_12_3005 : exactInterval 12 3005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3005 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3005) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3005 : oddCount 3005 12 = 8 ∧ acceleratedOrbit 12 3005 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3005 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3005) = 3 ^ 8 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3005.1, data_12_3005.2]

/-- Complete interval computation for depth 12, residue 3006. -/
theorem bounds_12_3006 : exactInterval 12 3006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3006 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3006) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3006 : oddCount 3006 12 = 8 ∧ acceleratedOrbit 12 3006 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3006 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3006) = 3 ^ 8 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3006.1, data_12_3006.2]

/-- Complete interval computation for depth 12, residue 3007. -/
theorem bounds_12_3007 : exactInterval 12 3007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3007 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3007) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3007 : oddCount 3007 12 = 9 ∧ acceleratedOrbit 12 3007 = 14455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3007 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3007) = 3 ^ 9 * m + 14455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3007.1, data_12_3007.2]

/-- Complete interval computation for depth 12, residue 3008. -/
theorem bounds_12_3008 : exactInterval 12 3008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3008 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3008) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3008 : oddCount 3008 12 = 5 ∧ acceleratedOrbit 12 3008 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3008 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3008) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3008.1, data_12_3008.2]

/-- Complete interval computation for depth 12, residue 3009. -/
theorem bounds_12_3009 : exactInterval 12 3009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3009 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3009) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3009 : oddCount 3009 12 = 7 ∧ acceleratedOrbit 12 3009 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3009 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3009) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3009.1, data_12_3009.2]

end Collatz.Research.StoppingAtlas.Batch0396
