import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0135

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1034. -/
theorem bounds_11_1034 : exactInterval 11 1034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1034 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1034) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1034 : oddCount 1034 11 = 5 ∧ acceleratedOrbit 11 1034 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1034 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1034) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1034.1, data_11_1034.2]

/-- Complete interval computation for depth 11, residue 1035. -/
theorem bounds_11_1035 : exactInterval 11 1035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1035 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1035) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1035 : oddCount 1035 11 = 4 ∧ acceleratedOrbit 11 1035 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1035 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1035) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1035.1, data_11_1035.2]

/-- Complete interval computation for depth 11, residue 1036. -/
theorem bounds_11_1036 : exactInterval 11 1036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1036 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1036) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1036 : oddCount 1036 11 = 5 ∧ acceleratedOrbit 11 1036 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1036 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1036) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1036.1, data_11_1036.2]

/-- Complete interval computation for depth 11, residue 1037. -/
theorem bounds_11_1037 : exactInterval 11 1037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1037 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1037) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1037 : oddCount 1037 11 = 5 ∧ acceleratedOrbit 11 1037 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1037 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1037) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1037.1, data_11_1037.2]

/-- Complete interval computation for depth 11, residue 1038. -/
theorem bounds_11_1038 : exactInterval 11 1038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1038 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1038) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1038 : oddCount 1038 11 = 6 ∧ acceleratedOrbit 11 1038 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1038 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1038) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1038.1, data_11_1038.2]

/-- Complete interval computation for depth 11, residue 1039. -/
theorem bounds_11_1039 : exactInterval 11 1039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1039 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1039) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1039 : oddCount 1039 11 = 6 ∧ acceleratedOrbit 11 1039 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1039 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1039) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1039.1, data_11_1039.2]

/-- Complete interval computation for depth 11, residue 1040. -/
theorem bounds_11_1040 : exactInterval 11 1040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1040 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1040) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1040 : oddCount 1040 11 = 3 ∧ acceleratedOrbit 11 1040 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1040 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1040) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1040.1, data_11_1040.2]

/-- Complete interval computation for depth 11, residue 1041. -/
theorem bounds_11_1041 : exactInterval 11 1041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1041 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1041) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1041 : oddCount 1041 11 = 5 ∧ acceleratedOrbit 11 1041 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1041 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1041) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1041.1, data_11_1041.2]

/-- Complete interval computation for depth 11, residue 1042. -/
theorem bounds_11_1042 : exactInterval 11 1042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1042 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1042) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1042 : oddCount 1042 11 = 5 ∧ acceleratedOrbit 11 1042 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1042 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1042) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1042.1, data_11_1042.2]

/-- Complete interval computation for depth 11, residue 1043. -/
theorem bounds_11_1043 : exactInterval 11 1043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1043 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1043) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1043 : oddCount 1043 11 = 5 ∧ acceleratedOrbit 11 1043 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1043 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1043) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1043.1, data_11_1043.2]

/-- Complete interval computation for depth 11, residue 1044. -/
theorem bounds_11_1044 : exactInterval 11 1044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1044 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1044) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1044 : oddCount 1044 11 = 3 ∧ acceleratedOrbit 11 1044 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1044 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1044) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1044.1, data_11_1044.2]

/-- Complete interval computation for depth 11, residue 1045. -/
theorem bounds_11_1045 : exactInterval 11 1045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1045 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1045) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1045 : oddCount 1045 11 = 3 ∧ acceleratedOrbit 11 1045 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1045 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1045) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1045.1, data_11_1045.2]

/-- Complete interval computation for depth 11, residue 1046. -/
theorem bounds_11_1046 : exactInterval 11 1046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1046 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1046) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1046 : oddCount 1046 11 = 5 ∧ acceleratedOrbit 11 1046 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1046 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1046) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1046.1, data_11_1046.2]

/-- Complete interval computation for depth 11, residue 1047. -/
theorem bounds_11_1047 : exactInterval 11 1047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1047 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1047) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1047 : oddCount 1047 11 = 5 ∧ acceleratedOrbit 11 1047 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1047 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1047) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1047.1, data_11_1047.2]

/-- Complete interval computation for depth 11, residue 1048. -/
theorem bounds_11_1048 : exactInterval 11 1048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1048 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1048) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1048 : oddCount 1048 11 = 3 ∧ acceleratedOrbit 11 1048 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1048 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1048) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1048.1, data_11_1048.2]

end Collatz.Research.StoppingAtlas.Batch0135
