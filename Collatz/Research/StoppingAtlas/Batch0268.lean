import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0268

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1029. -/
theorem bounds_12_1029 : exactInterval 12 1029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1029 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1029) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1029 : oddCount 1029 12 = 5 ∧ acceleratedOrbit 12 1029 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1029 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1029) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1029.1, data_12_1029.2]

/-- Complete interval computation for depth 12, residue 1030. -/
theorem bounds_12_1030 : exactInterval 12 1030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1030 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1030) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1030 : oddCount 1030 12 = 5 ∧ acceleratedOrbit 12 1030 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1030 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1030) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1030.1, data_12_1030.2]

/-- Complete interval computation for depth 12, residue 1031. -/
theorem bounds_12_1031 : exactInterval 12 1031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1031 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1031) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1031 : oddCount 1031 12 = 6 ∧ acceleratedOrbit 12 1031 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1031 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1031) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1031.1, data_12_1031.2]

/-- Complete interval computation for depth 12, residue 1032. -/
theorem bounds_12_1032 : exactInterval 12 1032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1032 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1032) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1032 : oddCount 1032 12 = 6 ∧ acceleratedOrbit 12 1032 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1032 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1032) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1032.1, data_12_1032.2]

/-- Complete interval computation for depth 12, residue 1033. -/
theorem bounds_12_1033 : exactInterval 12 1033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1033 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1033) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1033 : oddCount 1033 12 = 7 ∧ acceleratedOrbit 12 1033 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1033 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1033) = 3 ^ 7 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1033.1, data_12_1033.2]

/-- Complete interval computation for depth 12, residue 1034. -/
theorem bounds_12_1034 : exactInterval 12 1034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1034 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1034) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1034 : oddCount 1034 12 = 6 ∧ acceleratedOrbit 12 1034 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1034 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1034) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1034.1, data_12_1034.2]

/-- Complete interval computation for depth 12, residue 1035. -/
theorem bounds_12_1035 : exactInterval 12 1035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1035 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1035) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1035 : oddCount 1035 12 = 5 ∧ acceleratedOrbit 12 1035 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1035 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1035) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1035.1, data_12_1035.2]

/-- Complete interval computation for depth 12, residue 1036. -/
theorem bounds_12_1036 : exactInterval 12 1036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1036 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1036) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1036 : oddCount 1036 12 = 6 ∧ acceleratedOrbit 12 1036 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1036 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1036) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1036.1, data_12_1036.2]

/-- Complete interval computation for depth 12, residue 1037. -/
theorem bounds_12_1037 : exactInterval 12 1037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1037 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1037) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1037 : oddCount 1037 12 = 6 ∧ acceleratedOrbit 12 1037 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1037 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1037) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1037.1, data_12_1037.2]

/-- Complete interval computation for depth 12, residue 1038. -/
theorem bounds_12_1038 : exactInterval 12 1038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1038 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1038) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1038 : oddCount 1038 12 = 7 ∧ acceleratedOrbit 12 1038 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1038 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1038) = 3 ^ 7 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1038.1, data_12_1038.2]

/-- Complete interval computation for depth 12, residue 1039. -/
theorem bounds_12_1039 : exactInterval 12 1039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1039 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1039) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1039 : oddCount 1039 12 = 7 ∧ acceleratedOrbit 12 1039 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1039 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1039) = 3 ^ 7 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1039.1, data_12_1039.2]

/-- Complete interval computation for depth 12, residue 1040. -/
theorem bounds_12_1040 : exactInterval 12 1040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1040 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1040) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1040 : oddCount 1040 12 = 3 ∧ acceleratedOrbit 12 1040 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1040 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1040) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1040.1, data_12_1040.2]

/-- Complete interval computation for depth 12, residue 1041. -/
theorem bounds_12_1041 : exactInterval 12 1041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1041 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1041) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1041 : oddCount 1041 12 = 6 ∧ acceleratedOrbit 12 1041 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1041 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1041) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1041.1, data_12_1041.2]

/-- Complete interval computation for depth 12, residue 1042. -/
theorem bounds_12_1042 : exactInterval 12 1042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1042 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1042) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1042 : oddCount 1042 12 = 5 ∧ acceleratedOrbit 12 1042 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1042 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1042) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1042.1, data_12_1042.2]

/-- Complete interval computation for depth 12, residue 1043. -/
theorem bounds_12_1043 : exactInterval 12 1043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1043 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1043) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1043 : oddCount 1043 12 = 5 ∧ acceleratedOrbit 12 1043 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1043 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1043) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1043.1, data_12_1043.2]

end Collatz.Research.StoppingAtlas.Batch0268
