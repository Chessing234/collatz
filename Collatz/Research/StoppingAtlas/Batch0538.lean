import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0538

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1080. -/
theorem bounds_13_1080 : exactInterval 13 1080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1080 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1080) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1080 : oddCount 1080 13 = 6 ∧ acceleratedOrbit 13 1080 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1080 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1080) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1080.1, data_13_1080.2]

/-- Complete interval computation for depth 13, residue 1081. -/
theorem bounds_13_1081 : exactInterval 13 1081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1081 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1081) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1081 : oddCount 1081 13 = 7 ∧ acceleratedOrbit 13 1081 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1081 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1081) = 3 ^ 7 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1081.1, data_13_1081.2]

/-- Complete interval computation for depth 13, residue 1082. -/
theorem bounds_13_1082 : exactInterval 13 1082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1082 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1082) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1082 : oddCount 1082 13 = 6 ∧ acceleratedOrbit 13 1082 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1082 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1082) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1082.1, data_13_1082.2]

/-- Complete interval computation for depth 13, residue 1083. -/
theorem bounds_13_1083 : exactInterval 13 1083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1083 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1083) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1083 : oddCount 1083 13 = 7 ∧ acceleratedOrbit 13 1083 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1083 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1083) = 3 ^ 7 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1083.1, data_13_1083.2]

/-- Complete interval computation for depth 13, residue 1084. -/
theorem bounds_13_1084 : exactInterval 13 1084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1084 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1084) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1084 : oddCount 1084 13 = 6 ∧ acceleratedOrbit 13 1084 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1084 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1084) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1084.1, data_13_1084.2]

/-- Complete interval computation for depth 13, residue 1085. -/
theorem bounds_13_1085 : exactInterval 13 1085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1085 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1085) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1085 : oddCount 1085 13 = 6 ∧ acceleratedOrbit 13 1085 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1085 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1085) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1085.1, data_13_1085.2]

/-- Complete interval computation for depth 13, residue 1086. -/
theorem bounds_13_1086 : exactInterval 13 1086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1086 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1086) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1086 : oddCount 1086 13 = 8 ∧ acceleratedOrbit 13 1086 = 872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1086 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1086) = 3 ^ 8 * m + 872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1086.1, data_13_1086.2]

/-- Complete interval computation for depth 13, residue 1087. -/
theorem bounds_13_1087 : exactInterval 13 1087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1087 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1087) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1087 : oddCount 1087 13 = 8 ∧ acceleratedOrbit 13 1087 = 872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1087 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1087) = 3 ^ 8 * m + 872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1087.1, data_13_1087.2]

/-- Complete interval computation for depth 13, residue 1088. -/
theorem bounds_13_1088 : exactInterval 13 1088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1088 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1088) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1088 : oddCount 1088 13 = 3 ∧ acceleratedOrbit 13 1088 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1088 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1088) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1088.1, data_13_1088.2]

/-- Complete interval computation for depth 13, residue 1089. -/
theorem bounds_13_1089 : exactInterval 13 1089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1089 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1089) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1089 : oddCount 1089 13 = 6 ∧ acceleratedOrbit 13 1089 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1089 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1089) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1089.1, data_13_1089.2]

/-- Complete interval computation for depth 13, residue 1090. -/
theorem bounds_13_1090 : exactInterval 13 1090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1090 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1090) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1090 : oddCount 1090 13 = 6 ∧ acceleratedOrbit 13 1090 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1090 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1090) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1090.1, data_13_1090.2]

/-- Complete interval computation for depth 13, residue 1091. -/
theorem bounds_13_1091 : exactInterval 13 1091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1091 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1091) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1091 : oddCount 1091 13 = 6 ∧ acceleratedOrbit 13 1091 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1091 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1091) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1091.1, data_13_1091.2]

/-- Complete interval computation for depth 13, residue 1092. -/
theorem bounds_13_1092 : exactInterval 13 1092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1092 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1092) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1092 : oddCount 1092 13 = 4 ∧ acceleratedOrbit 13 1092 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1092 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1092) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1092.1, data_13_1092.2]

/-- Complete interval computation for depth 13, residue 1093. -/
theorem bounds_13_1093 : exactInterval 13 1093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1093 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1093) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1093 : oddCount 1093 13 = 4 ∧ acceleratedOrbit 13 1093 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1093 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1093) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1093.1, data_13_1093.2]

/-- Complete interval computation for depth 13, residue 1094. -/
theorem bounds_13_1094 : exactInterval 13 1094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1094 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1094) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1094 : oddCount 1094 13 = 4 ∧ acceleratedOrbit 13 1094 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1094 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1094) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1094.1, data_13_1094.2]

end Collatz.Research.StoppingAtlas.Batch0538
