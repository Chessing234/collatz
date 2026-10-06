import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0138

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1080. -/
theorem bounds_11_1080 : exactInterval 11 1080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1080 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1080) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1080 : oddCount 1080 11 = 4 ∧ acceleratedOrbit 11 1080 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1080 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1080) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1080.1, data_11_1080.2]

/-- Complete interval computation for depth 11, residue 1081. -/
theorem bounds_11_1081 : exactInterval 11 1081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1081 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1081) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1081 : oddCount 1081 11 = 6 ∧ acceleratedOrbit 11 1081 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1081 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1081) = 3 ^ 6 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1081.1, data_11_1081.2]

/-- Complete interval computation for depth 11, residue 1082. -/
theorem bounds_11_1082 : exactInterval 11 1082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1082 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1082) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1082 : oddCount 1082 11 = 4 ∧ acceleratedOrbit 11 1082 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1082 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1082) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1082.1, data_11_1082.2]

/-- Complete interval computation for depth 11, residue 1083. -/
theorem bounds_11_1083 : exactInterval 11 1083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1083 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1083) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1083 : oddCount 1083 11 = 7 ∧ acceleratedOrbit 11 1083 = 1160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1083 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1083) = 3 ^ 7 * m + 1160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1083.1, data_11_1083.2]

/-- Complete interval computation for depth 11, residue 1084. -/
theorem bounds_11_1084 : exactInterval 11 1084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1084 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1084) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1084 : oddCount 1084 11 = 4 ∧ acceleratedOrbit 11 1084 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1084 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1084) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1084.1, data_11_1084.2]

/-- Complete interval computation for depth 11, residue 1085. -/
theorem bounds_11_1085 : exactInterval 11 1085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1085 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1085) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1085 : oddCount 1085 11 = 4 ∧ acceleratedOrbit 11 1085 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1085 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1085) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1085.1, data_11_1085.2]

/-- Complete interval computation for depth 11, residue 1086. -/
theorem bounds_11_1086 : exactInterval 11 1086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1086 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1086) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1086 : oddCount 1086 11 = 7 ∧ acceleratedOrbit 11 1086 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1086 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1086) = 3 ^ 7 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1086.1, data_11_1086.2]

/-- Complete interval computation for depth 11, residue 1087. -/
theorem bounds_11_1087 : exactInterval 11 1087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1087 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1087) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1087 : oddCount 1087 11 = 7 ∧ acceleratedOrbit 11 1087 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1087 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1087) = 3 ^ 7 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1087.1, data_11_1087.2]

/-- Complete interval computation for depth 11, residue 1088. -/
theorem bounds_11_1088 : exactInterval 11 1088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1088 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1088) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1088 : oddCount 1088 11 = 2 ∧ acceleratedOrbit 11 1088 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1088 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1088) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1088.1, data_11_1088.2]

/-- Complete interval computation for depth 11, residue 1089. -/
theorem bounds_11_1089 : exactInterval 11 1089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1089 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1089) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1089 : oddCount 1089 11 = 5 ∧ acceleratedOrbit 11 1089 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1089 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1089) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1089.1, data_11_1089.2]

/-- Complete interval computation for depth 11, residue 1090. -/
theorem bounds_11_1090 : exactInterval 11 1090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1090 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1090) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1090 : oddCount 1090 11 = 5 ∧ acceleratedOrbit 11 1090 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1090 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1090) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1090.1, data_11_1090.2]

/-- Complete interval computation for depth 11, residue 1091. -/
theorem bounds_11_1091 : exactInterval 11 1091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1091 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1091) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1091 : oddCount 1091 11 = 5 ∧ acceleratedOrbit 11 1091 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1091 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1091) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1091.1, data_11_1091.2]

/-- Complete interval computation for depth 11, residue 1092. -/
theorem bounds_11_1092 : exactInterval 11 1092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1092 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1092) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1092 : oddCount 1092 11 = 4 ∧ acceleratedOrbit 11 1092 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1092 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1092) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1092.1, data_11_1092.2]

/-- Complete interval computation for depth 11, residue 1093. -/
theorem bounds_11_1093 : exactInterval 11 1093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1093 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1093) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1093 : oddCount 1093 11 = 4 ∧ acceleratedOrbit 11 1093 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1093 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1093) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1093.1, data_11_1093.2]

/-- Complete interval computation for depth 11, residue 1094. -/
theorem bounds_11_1094 : exactInterval 11 1094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1094 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1094) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1094 : oddCount 1094 11 = 4 ∧ acceleratedOrbit 11 1094 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1094 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1094) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1094.1, data_11_1094.2]

end Collatz.Research.StoppingAtlas.Batch0138
