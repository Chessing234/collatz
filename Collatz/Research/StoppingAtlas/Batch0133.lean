import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0133

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1003. -/
theorem bounds_11_1003 : exactInterval 11 1003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1003 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1003) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1003 : oddCount 1003 11 = 7 ∧ acceleratedOrbit 11 1003 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1003 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1003) = 3 ^ 7 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1003.1, data_11_1003.2]

/-- Complete interval computation for depth 11, residue 1004. -/
theorem bounds_11_1004 : exactInterval 11 1004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1004 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1004) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1004 : oddCount 1004 11 = 7 ∧ acceleratedOrbit 11 1004 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1004 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1004) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1004.1, data_11_1004.2]

/-- Complete interval computation for depth 11, residue 1005. -/
theorem bounds_11_1005 : exactInterval 11 1005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1005 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1005) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1005 : oddCount 1005 11 = 7 ∧ acceleratedOrbit 11 1005 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1005 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1005) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1005.1, data_11_1005.2]

/-- Complete interval computation for depth 11, residue 1006. -/
theorem bounds_11_1006 : exactInterval 11 1006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1006 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1006) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1006 : oddCount 1006 11 = 7 ∧ acceleratedOrbit 11 1006 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1006 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1006) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1006.1, data_11_1006.2]

/-- Complete interval computation for depth 11, residue 1007. -/
theorem bounds_11_1007 : exactInterval 11 1007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1007 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1007) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1007 : oddCount 1007 11 = 8 ∧ acceleratedOrbit 11 1007 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1007 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1007) = 3 ^ 8 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1007.1, data_11_1007.2]

/-- Complete interval computation for depth 11, residue 1008. -/
theorem bounds_11_1008 : exactInterval 11 1008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1008 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1008) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1008 : oddCount 1008 11 = 6 ∧ acceleratedOrbit 11 1008 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1008 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1008) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1008.1, data_11_1008.2]

/-- Complete interval computation for depth 11, residue 1009. -/
theorem bounds_11_1009 : exactInterval 11 1009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1009 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1009) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1009 : oddCount 1009 11 = 5 ∧ acceleratedOrbit 11 1009 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1009 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1009) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1009.1, data_11_1009.2]

/-- Complete interval computation for depth 11, residue 1010. -/
theorem bounds_11_1010 : exactInterval 11 1010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1010 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1010) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1010 : oddCount 1010 11 = 6 ∧ acceleratedOrbit 11 1010 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1010 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1010) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1010.1, data_11_1010.2]

/-- Complete interval computation for depth 11, residue 1011. -/
theorem bounds_11_1011 : exactInterval 11 1011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1011 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1011) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1011 : oddCount 1011 11 = 6 ∧ acceleratedOrbit 11 1011 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1011 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1011) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1011.1, data_11_1011.2]

/-- Complete interval computation for depth 11, residue 1012. -/
theorem bounds_11_1012 : exactInterval 11 1012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1012 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1012) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1012 : oddCount 1012 11 = 6 ∧ acceleratedOrbit 11 1012 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1012 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1012) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1012.1, data_11_1012.2]

/-- Complete interval computation for depth 11, residue 1013. -/
theorem bounds_11_1013 : exactInterval 11 1013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1013 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1013) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1013 : oddCount 1013 11 = 6 ∧ acceleratedOrbit 11 1013 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1013 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1013) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1013.1, data_11_1013.2]

/-- Complete interval computation for depth 11, residue 1014. -/
theorem bounds_11_1014 : exactInterval 11 1014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1014 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1014) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1014 : oddCount 1014 11 = 6 ∧ acceleratedOrbit 11 1014 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1014 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1014) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1014.1, data_11_1014.2]

/-- Complete interval computation for depth 11, residue 1015. -/
theorem bounds_11_1015 : exactInterval 11 1015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1015 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1015) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1015 : oddCount 1015 11 = 6 ∧ acceleratedOrbit 11 1015 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1015 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1015) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1015.1, data_11_1015.2]

/-- Complete interval computation for depth 11, residue 1016. -/
theorem bounds_11_1016 : exactInterval 11 1016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1016 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1016) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1016 : oddCount 1016 11 = 7 ∧ acceleratedOrbit 11 1016 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1016 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1016) = 3 ^ 7 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1016.1, data_11_1016.2]

/-- Complete interval computation for depth 11, residue 1017. -/
theorem bounds_11_1017 : exactInterval 11 1017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1017 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1017) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1017 : oddCount 1017 11 = 8 ∧ acceleratedOrbit 11 1017 = 3266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1017 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1017) = 3 ^ 8 * m + 3266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1017.1, data_11_1017.2]

end Collatz.Research.StoppingAtlas.Batch0133
