import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0535

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1034. -/
theorem bounds_13_1034 : exactInterval 13 1034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1034 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1034) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1034 : oddCount 1034 13 = 6 ∧ acceleratedOrbit 13 1034 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1034 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1034) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1034.1, data_13_1034.2]

/-- Complete interval computation for depth 13, residue 1035. -/
theorem bounds_13_1035 : exactInterval 13 1035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1035 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1035) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1035 : oddCount 1035 13 = 5 ∧ acceleratedOrbit 13 1035 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1035 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1035) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1035.1, data_13_1035.2]

/-- Complete interval computation for depth 13, residue 1036. -/
theorem bounds_13_1036 : exactInterval 13 1036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1036 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1036) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1036 : oddCount 1036 13 = 6 ∧ acceleratedOrbit 13 1036 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1036 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1036) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1036.1, data_13_1036.2]

/-- Complete interval computation for depth 13, residue 1037. -/
theorem bounds_13_1037 : exactInterval 13 1037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1037 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1037) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1037 : oddCount 1037 13 = 6 ∧ acceleratedOrbit 13 1037 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1037 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1037) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1037.1, data_13_1037.2]

/-- Complete interval computation for depth 13, residue 1038. -/
theorem bounds_13_1038 : exactInterval 13 1038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1038 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1038) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1038 : oddCount 1038 13 = 8 ∧ acceleratedOrbit 13 1038 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1038 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1038) = 3 ^ 8 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1038.1, data_13_1038.2]

/-- Complete interval computation for depth 13, residue 1039. -/
theorem bounds_13_1039 : exactInterval 13 1039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1039 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1039) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1039 : oddCount 1039 13 = 8 ∧ acceleratedOrbit 13 1039 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1039 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1039) = 3 ^ 8 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1039.1, data_13_1039.2]

/-- Complete interval computation for depth 13, residue 1040. -/
theorem bounds_13_1040 : exactInterval 13 1040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1040 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1040) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1040 : oddCount 1040 13 = 4 ∧ acceleratedOrbit 13 1040 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1040 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1040) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1040.1, data_13_1040.2]

/-- Complete interval computation for depth 13, residue 1041. -/
theorem bounds_13_1041 : exactInterval 13 1041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1041 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1041) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1041 : oddCount 1041 13 = 6 ∧ acceleratedOrbit 13 1041 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1041 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1041) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1041.1, data_13_1041.2]

/-- Complete interval computation for depth 13, residue 1042. -/
theorem bounds_13_1042 : exactInterval 13 1042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1042 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1042) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1042 : oddCount 1042 13 = 5 ∧ acceleratedOrbit 13 1042 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1042 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1042) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1042.1, data_13_1042.2]

/-- Complete interval computation for depth 13, residue 1043. -/
theorem bounds_13_1043 : exactInterval 13 1043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1043 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1043) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1043 : oddCount 1043 13 = 5 ∧ acceleratedOrbit 13 1043 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1043 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1043) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1043.1, data_13_1043.2]

/-- Complete interval computation for depth 13, residue 1044. -/
theorem bounds_13_1044 : exactInterval 13 1044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1044 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1044) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1044 : oddCount 1044 13 = 4 ∧ acceleratedOrbit 13 1044 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1044 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1044) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1044.1, data_13_1044.2]

/-- Complete interval computation for depth 13, residue 1045. -/
theorem bounds_13_1045 : exactInterval 13 1045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1045 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1045) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1045 : oddCount 1045 13 = 4 ∧ acceleratedOrbit 13 1045 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1045 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1045) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1045.1, data_13_1045.2]

/-- Complete interval computation for depth 13, residue 1046. -/
theorem bounds_13_1046 : exactInterval 13 1046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1046 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1046) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1046 : oddCount 1046 13 = 6 ∧ acceleratedOrbit 13 1046 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1046 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1046) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1046.1, data_13_1046.2]

/-- Complete interval computation for depth 13, residue 1047. -/
theorem bounds_13_1047 : exactInterval 13 1047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1047 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1047) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1047 : oddCount 1047 13 = 6 ∧ acceleratedOrbit 13 1047 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1047 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1047) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1047.1, data_13_1047.2]

/-- Complete interval computation for depth 13, residue 1048. -/
theorem bounds_13_1048 : exactInterval 13 1048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1048 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1048) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1048 : oddCount 1048 13 = 4 ∧ acceleratedOrbit 13 1048 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1048 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1048) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1048.1, data_13_1048.2]

end Collatz.Research.StoppingAtlas.Batch0535
