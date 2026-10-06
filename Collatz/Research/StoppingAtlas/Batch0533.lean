import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0533

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1003. -/
theorem bounds_13_1003 : exactInterval 13 1003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1003 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1003) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1003 : oddCount 1003 13 = 8 ∧ acceleratedOrbit 13 1003 = 805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1003 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1003) = 3 ^ 8 * m + 805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1003.1, data_13_1003.2]

/-- Complete interval computation for depth 13, residue 1004. -/
theorem bounds_13_1004 : exactInterval 13 1004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1004 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1004) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1004 : oddCount 1004 13 = 9 ∧ acceleratedOrbit 13 1004 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1004 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1004) = 3 ^ 9 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1004.1, data_13_1004.2]

/-- Complete interval computation for depth 13, residue 1005. -/
theorem bounds_13_1005 : exactInterval 13 1005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1005 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1005) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1005 : oddCount 1005 13 = 9 ∧ acceleratedOrbit 13 1005 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1005 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1005) = 3 ^ 9 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1005.1, data_13_1005.2]

/-- Complete interval computation for depth 13, residue 1006. -/
theorem bounds_13_1006 : exactInterval 13 1006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1006 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1006) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1006 : oddCount 1006 13 = 9 ∧ acceleratedOrbit 13 1006 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1006 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1006) = 3 ^ 9 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1006.1, data_13_1006.2]

/-- Complete interval computation for depth 13, residue 1007. -/
theorem bounds_13_1007 : exactInterval 13 1007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1007 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1007) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1007 : oddCount 1007 13 = 9 ∧ acceleratedOrbit 13 1007 = 2423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1007 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1007) = 3 ^ 9 * m + 2423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1007.1, data_13_1007.2]

/-- Complete interval computation for depth 13, residue 1008. -/
theorem bounds_13_1008 : exactInterval 13 1008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1008 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1008) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1008 : oddCount 1008 13 = 6 ∧ acceleratedOrbit 13 1008 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1008 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1008) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1008.1, data_13_1008.2]

/-- Complete interval computation for depth 13, residue 1009. -/
theorem bounds_13_1009 : exactInterval 13 1009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1009 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1009) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1009 : oddCount 1009 13 = 6 ∧ acceleratedOrbit 13 1009 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1009 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1009) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1009.1, data_13_1009.2]

/-- Complete interval computation for depth 13, residue 1010. -/
theorem bounds_13_1010 : exactInterval 13 1010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1010 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1010) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1010 : oddCount 1010 13 = 7 ∧ acceleratedOrbit 13 1010 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1010 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1010) = 3 ^ 7 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1010.1, data_13_1010.2]

/-- Complete interval computation for depth 13, residue 1011. -/
theorem bounds_13_1011 : exactInterval 13 1011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1011 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1011) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1011 : oddCount 1011 13 = 7 ∧ acceleratedOrbit 13 1011 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1011 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1011) = 3 ^ 7 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1011.1, data_13_1011.2]

/-- Complete interval computation for depth 13, residue 1012. -/
theorem bounds_13_1012 : exactInterval 13 1012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1012 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1012) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1012 : oddCount 1012 13 = 6 ∧ acceleratedOrbit 13 1012 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1012 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1012) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1012.1, data_13_1012.2]

/-- Complete interval computation for depth 13, residue 1013. -/
theorem bounds_13_1013 : exactInterval 13 1013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1013 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1013) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1013 : oddCount 1013 13 = 6 ∧ acceleratedOrbit 13 1013 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1013 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1013) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1013.1, data_13_1013.2]

/-- Complete interval computation for depth 13, residue 1014. -/
theorem bounds_13_1014 : exactInterval 13 1014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1014 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1014) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1014 : oddCount 1014 13 = 7 ∧ acceleratedOrbit 13 1014 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1014 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1014) = 3 ^ 7 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1014.1, data_13_1014.2]

/-- Complete interval computation for depth 13, residue 1015. -/
theorem bounds_13_1015 : exactInterval 13 1015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1015 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1015) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1015 : oddCount 1015 13 = 7 ∧ acceleratedOrbit 13 1015 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1015 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1015) = 3 ^ 7 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1015.1, data_13_1015.2]

/-- Complete interval computation for depth 13, residue 1016. -/
theorem bounds_13_1016 : exactInterval 13 1016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1016 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1016) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1016 : oddCount 1016 13 = 8 ∧ acceleratedOrbit 13 1016 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1016 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1016) = 3 ^ 8 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1016.1, data_13_1016.2]

/-- Complete interval computation for depth 13, residue 1017. -/
theorem bounds_13_1017 : exactInterval 13 1017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1017 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1017) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1017 : oddCount 1017 13 = 9 ∧ acceleratedOrbit 13 1017 = 2450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1017 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1017) = 3 ^ 9 * m + 2450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1017.1, data_13_1017.2]

end Collatz.Research.StoppingAtlas.Batch0533
