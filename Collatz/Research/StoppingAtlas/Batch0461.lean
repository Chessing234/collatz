import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0461

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3993. -/
theorem bounds_12_3993 : exactInterval 12 3993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3993 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3993) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3993 : oddCount 3993 12 = 4 ∧ acceleratedOrbit 12 3993 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3993 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3993) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3993.1, data_12_3993.2]

/-- Complete interval computation for depth 12, residue 3994. -/
theorem bounds_12_3994 : exactInterval 12 3994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3994 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3994) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3994 : oddCount 3994 12 = 5 ∧ acceleratedOrbit 12 3994 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3994 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3994) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3994.1, data_12_3994.2]

/-- Complete interval computation for depth 12, residue 3995. -/
theorem bounds_12_3995 : exactInterval 12 3995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3995 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3995) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3995 : oddCount 3995 12 = 7 ∧ acceleratedOrbit 12 3995 = 2134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3995 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3995) = 3 ^ 7 * m + 2134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3995.1, data_12_3995.2]

/-- Complete interval computation for depth 12, residue 3996. -/
theorem bounds_12_3996 : exactInterval 12 3996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3996 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3996) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3996 : oddCount 3996 12 = 6 ∧ acceleratedOrbit 12 3996 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3996 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3996) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3996.1, data_12_3996.2]

/-- Complete interval computation for depth 12, residue 3997. -/
theorem bounds_12_3997 : exactInterval 12 3997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3997 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3997) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3997 : oddCount 3997 12 = 6 ∧ acceleratedOrbit 12 3997 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3997 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3997) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3997.1, data_12_3997.2]

/-- Complete interval computation for depth 12, residue 3998. -/
theorem bounds_12_3998 : exactInterval 12 3998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3998 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3998) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3998 : oddCount 3998 12 = 6 ∧ acceleratedOrbit 12 3998 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3998 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3998) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3998.1, data_12_3998.2]

/-- Complete interval computation for depth 12, residue 3999. -/
theorem bounds_12_3999 : exactInterval 12 3999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3999 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3999) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3999 : oddCount 3999 12 = 9 ∧ acceleratedOrbit 12 3999 = 19223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3999 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3999) = 3 ^ 9 * m + 19223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3999.1, data_12_3999.2]

/-- Complete interval computation for depth 12, residue 4000. -/
theorem bounds_12_4000 : exactInterval 12 4000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4000 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4000) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4000 : oddCount 4000 12 = 5 ∧ acceleratedOrbit 12 4000 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4000 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4000) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4000.1, data_12_4000.2]

/-- Complete interval computation for depth 12, residue 4001. -/
theorem bounds_12_4001 : exactInterval 12 4001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4001 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4001) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4001 : oddCount 4001 12 = 6 ∧ acceleratedOrbit 12 4001 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4001 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4001) = 3 ^ 6 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4001.1, data_12_4001.2]

/-- Complete interval computation for depth 12, residue 4002. -/
theorem bounds_12_4002 : exactInterval 12 4002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4002 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4002) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4002 : oddCount 4002 12 = 5 ∧ acceleratedOrbit 12 4002 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4002 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4002) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4002.1, data_12_4002.2]

/-- Complete interval computation for depth 12, residue 4003. -/
theorem bounds_12_4003 : exactInterval 12 4003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4003 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4003) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4003 : oddCount 4003 12 = 5 ∧ acceleratedOrbit 12 4003 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4003 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4003) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4003.1, data_12_4003.2]

/-- Complete interval computation for depth 12, residue 4004. -/
theorem bounds_12_4004 : exactInterval 12 4004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4004 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4004) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4004 : oddCount 4004 12 = 8 ∧ acceleratedOrbit 12 4004 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4004 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4004) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4004.1, data_12_4004.2]

/-- Complete interval computation for depth 12, residue 4005. -/
theorem bounds_12_4005 : exactInterval 12 4005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4005 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4005) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4005 : oddCount 4005 12 = 8 ∧ acceleratedOrbit 12 4005 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4005 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4005) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4005.1, data_12_4005.2]

/-- Complete interval computation for depth 12, residue 4006. -/
theorem bounds_12_4006 : exactInterval 12 4006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4006 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4006) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4006 : oddCount 4006 12 = 8 ∧ acceleratedOrbit 12 4006 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4006 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4006) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4006.1, data_12_4006.2]

/-- Complete interval computation for depth 12, residue 4007. -/
theorem bounds_12_4007 : exactInterval 12 4007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4007 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4007) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4007 : oddCount 4007 12 = 8 ∧ acceleratedOrbit 12 4007 = 6421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4007 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4007) = 3 ^ 8 * m + 6421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4007.1, data_12_4007.2]

end Collatz.Research.StoppingAtlas.Batch0461
