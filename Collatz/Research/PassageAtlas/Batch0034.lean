import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0034

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1081. -/
theorem bounds_15_1081 : exactInterval 15 1081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1081 : oddCount 1081 15 = 8 ∧ acceleratedOrbit 15 1081 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1081) = 3 ^ 8 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1081.1, data_15_1081.2]

/-- Complete interval computation for depth 15, residue 1082. -/
theorem bounds_15_1082 : exactInterval 15 1082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1082 : oddCount 1082 15 = 7 ∧ acceleratedOrbit 15 1082 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1082) = 3 ^ 7 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1082.1, data_15_1082.2]

/-- Complete interval computation for depth 15, residue 1083. -/
theorem bounds_15_1083 : exactInterval 15 1083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1083 : oddCount 1083 15 = 8 ∧ acceleratedOrbit 15 1083 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1083) = 3 ^ 8 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1083.1, data_15_1083.2]

/-- Complete interval computation for depth 15, residue 1084. -/
theorem bounds_15_1084 : exactInterval 15 1084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1084 : oddCount 1084 15 = 7 ∧ acceleratedOrbit 15 1084 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1084) = 3 ^ 7 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1084.1, data_15_1084.2]

/-- Complete interval computation for depth 15, residue 1085. -/
theorem bounds_15_1085 : exactInterval 15 1085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1085 : oddCount 1085 15 = 7 ∧ acceleratedOrbit 15 1085 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1085) = 3 ^ 7 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1085.1, data_15_1085.2]

/-- Complete interval computation for depth 15, residue 1086. -/
theorem bounds_15_1086 : exactInterval 15 1086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1086 : oddCount 1086 15 = 8 ∧ acceleratedOrbit 15 1086 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1086) = 3 ^ 8 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1086.1, data_15_1086.2]

/-- Complete interval computation for depth 15, residue 1087. -/
theorem bounds_15_1087 : exactInterval 15 1087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1087 : oddCount 1087 15 = 8 ∧ acceleratedOrbit 15 1087 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1087) = 3 ^ 8 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1087.1, data_15_1087.2]

/-- Complete interval computation for depth 15, residue 1088. -/
theorem bounds_15_1088 : exactInterval 15 1088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1088 : oddCount 1088 15 = 3 ∧ acceleratedOrbit 15 1088 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1088) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1088.1, data_15_1088.2]

/-- Complete interval computation for depth 15, residue 1089. -/
theorem bounds_15_1089 : exactInterval 15 1089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1089 : oddCount 1089 15 = 7 ∧ acceleratedOrbit 15 1089 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1089) = 3 ^ 7 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1089.1, data_15_1089.2]

/-- Complete interval computation for depth 15, residue 1090. -/
theorem bounds_15_1090 : exactInterval 15 1090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1090 : oddCount 1090 15 = 7 ∧ acceleratedOrbit 15 1090 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1090) = 3 ^ 7 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1090.1, data_15_1090.2]

/-- Complete interval computation for depth 15, residue 1091. -/
theorem bounds_15_1091 : exactInterval 15 1091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1091 : oddCount 1091 15 = 7 ∧ acceleratedOrbit 15 1091 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1091) = 3 ^ 7 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1091.1, data_15_1091.2]

/-- Complete interval computation for depth 15, residue 1092. -/
theorem bounds_15_1092 : exactInterval 15 1092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1092 : oddCount 1092 15 = 6 ∧ acceleratedOrbit 15 1092 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1092) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1092.1, data_15_1092.2]

/-- Complete interval computation for depth 15, residue 1093. -/
theorem bounds_15_1093 : exactInterval 15 1093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1093 : oddCount 1093 15 = 6 ∧ acceleratedOrbit 15 1093 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1093) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1093.1, data_15_1093.2]

/-- Complete interval computation for depth 15, residue 1094. -/
theorem bounds_15_1094 : exactInterval 15 1094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1094 : oddCount 1094 15 = 6 ∧ acceleratedOrbit 15 1094 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1094) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1094.1, data_15_1094.2]

/-- Complete interval computation for depth 15, residue 1095. -/
theorem bounds_15_1095 : exactInterval 15 1095 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1095) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1095 : oddCount 1095 15 = 9 ∧ acceleratedOrbit 15 1095 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1095) = 3 ^ 9 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1095.1, data_15_1095.2]

/-- Complete interval computation for depth 15, residue 1096. -/
theorem bounds_15_1096 : exactInterval 15 1096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1096 : oddCount 1096 15 = 9 ∧ acceleratedOrbit 15 1096 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1096) = 3 ^ 9 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1096.1, data_15_1096.2]

/-- Complete interval computation for depth 15, residue 1097. -/
theorem bounds_15_1097 : exactInterval 15 1097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1097 : oddCount 1097 15 = 9 ∧ acceleratedOrbit 15 1097 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1097) = 3 ^ 9 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1097.1, data_15_1097.2]

/-- Complete interval computation for depth 15, residue 1098. -/
theorem bounds_15_1098 : exactInterval 15 1098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1098 : oddCount 1098 15 = 9 ∧ acceleratedOrbit 15 1098 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1098) = 3 ^ 9 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1098.1, data_15_1098.2]

/-- Complete interval computation for depth 15, residue 1099. -/
theorem bounds_15_1099 : exactInterval 15 1099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1099 : oddCount 1099 15 = 6 ∧ acceleratedOrbit 15 1099 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1099) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1099.1, data_15_1099.2]

/-- Complete interval computation for depth 15, residue 1100. -/
theorem bounds_15_1100 : exactInterval 15 1100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1100 : oddCount 1100 15 = 9 ∧ acceleratedOrbit 15 1100 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1100) = 3 ^ 9 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1100.1, data_15_1100.2]

/-- Complete interval computation for depth 15, residue 1101. -/
theorem bounds_15_1101 : exactInterval 15 1101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1101 : oddCount 1101 15 = 9 ∧ acceleratedOrbit 15 1101 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1101) = 3 ^ 9 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1101.1, data_15_1101.2]

/-- Complete interval computation for depth 15, residue 1102. -/
theorem bounds_15_1102 : exactInterval 15 1102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1102 : oddCount 1102 15 = 7 ∧ acceleratedOrbit 15 1102 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1102) = 3 ^ 7 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1102.1, data_15_1102.2]

/-- Complete interval computation for depth 15, residue 1103. -/
theorem bounds_15_1103 : exactInterval 15 1103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1103 : oddCount 1103 15 = 7 ∧ acceleratedOrbit 15 1103 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1103) = 3 ^ 7 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1103.1, data_15_1103.2]

/-- Complete interval computation for depth 15, residue 1104. -/
theorem bounds_15_1104 : exactInterval 15 1104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1104 : oddCount 1104 15 = 3 ∧ acceleratedOrbit 15 1104 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1104) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1104.1, data_15_1104.2]

/-- Complete interval computation for depth 15, residue 1105. -/
theorem bounds_15_1105 : exactInterval 15 1105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1105 : oddCount 1105 15 = 9 ∧ acceleratedOrbit 15 1105 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1105) = 3 ^ 9 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1105.1, data_15_1105.2]

/-- Complete interval computation for depth 15, residue 1106. -/
theorem bounds_15_1106 : exactInterval 15 1106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1106 : oddCount 1106 15 = 10 ∧ acceleratedOrbit 15 1106 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1106) = 3 ^ 10 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1106.1, data_15_1106.2]

/-- Complete interval computation for depth 15, residue 1107. -/
theorem bounds_15_1107 : exactInterval 15 1107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1107 : oddCount 1107 15 = 10 ∧ acceleratedOrbit 15 1107 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1107) = 3 ^ 10 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1107.1, data_15_1107.2]

/-- Complete interval computation for depth 15, residue 1108. -/
theorem bounds_15_1108 : exactInterval 15 1108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1108 : oddCount 1108 15 = 3 ∧ acceleratedOrbit 15 1108 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1108) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1108.1, data_15_1108.2]

/-- Complete interval computation for depth 15, residue 1109. -/
theorem bounds_15_1109 : exactInterval 15 1109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1109 : oddCount 1109 15 = 3 ∧ acceleratedOrbit 15 1109 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1109) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1109.1, data_15_1109.2]

/-- Complete interval computation for depth 15, residue 1110. -/
theorem bounds_15_1110 : exactInterval 15 1110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1110 : oddCount 1110 15 = 6 ∧ acceleratedOrbit 15 1110 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1110) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1110.1, data_15_1110.2]

/-- Complete interval computation for depth 15, residue 1111. -/
theorem bounds_15_1111 : exactInterval 15 1111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1111 : oddCount 1111 15 = 6 ∧ acceleratedOrbit 15 1111 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1111) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1111.1, data_15_1111.2]

/-- Complete interval computation for depth 15, residue 1112. -/
theorem bounds_15_1112 : exactInterval 15 1112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1112 : oddCount 1112 15 = 7 ∧ acceleratedOrbit 15 1112 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1112) = 3 ^ 7 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1112.1, data_15_1112.2]

/-- Complete interval computation for depth 15, residue 1113. -/
theorem bounds_15_1113 : exactInterval 15 1113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1113 : oddCount 1113 15 = 9 ∧ acceleratedOrbit 15 1113 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1113) = 3 ^ 9 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1113.1, data_15_1113.2]

end Collatz.Research.PassageAtlas.Batch0034
