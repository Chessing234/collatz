import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0271

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1075. -/
theorem bounds_12_1075 : exactInterval 12 1075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1075 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1075) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1075 : oddCount 1075 12 = 5 ∧ acceleratedOrbit 12 1075 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1075 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1075) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1075.1, data_12_1075.2]

/-- Complete interval computation for depth 12, residue 1076. -/
theorem bounds_12_1076 : exactInterval 12 1076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1076 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1076) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1076 : oddCount 1076 12 = 4 ∧ acceleratedOrbit 12 1076 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1076 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1076) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1076.1, data_12_1076.2]

/-- Complete interval computation for depth 12, residue 1077. -/
theorem bounds_12_1077 : exactInterval 12 1077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1077 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1077) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1077 : oddCount 1077 12 = 4 ∧ acceleratedOrbit 12 1077 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1077 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1077) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1077.1, data_12_1077.2]

/-- Complete interval computation for depth 12, residue 1078. -/
theorem bounds_12_1078 : exactInterval 12 1078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1078 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1078) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1078 : oddCount 1078 12 = 7 ∧ acceleratedOrbit 12 1078 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1078 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1078) = 3 ^ 7 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1078.1, data_12_1078.2]

/-- Complete interval computation for depth 12, residue 1079. -/
theorem bounds_12_1079 : exactInterval 12 1079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1079 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1079) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1079 : oddCount 1079 12 = 7 ∧ acceleratedOrbit 12 1079 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1079 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1079) = 3 ^ 7 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1079.1, data_12_1079.2]

/-- Complete interval computation for depth 12, residue 1080. -/
theorem bounds_12_1080 : exactInterval 12 1080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1080 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1080) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1080 : oddCount 1080 12 = 5 ∧ acceleratedOrbit 12 1080 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1080 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1080) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1080.1, data_12_1080.2]

/-- Complete interval computation for depth 12, residue 1081. -/
theorem bounds_12_1081 : exactInterval 12 1081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1081 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1081) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1081 : oddCount 1081 12 = 6 ∧ acceleratedOrbit 12 1081 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1081 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1081) = 3 ^ 6 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1081.1, data_12_1081.2]

/-- Complete interval computation for depth 12, residue 1082. -/
theorem bounds_12_1082 : exactInterval 12 1082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1082 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1082) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1082 : oddCount 1082 12 = 5 ∧ acceleratedOrbit 12 1082 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1082 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1082) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1082.1, data_12_1082.2]

/-- Complete interval computation for depth 12, residue 1083. -/
theorem bounds_12_1083 : exactInterval 12 1083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1083 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1083) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1083 : oddCount 1083 12 = 7 ∧ acceleratedOrbit 12 1083 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1083 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1083) = 3 ^ 7 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1083.1, data_12_1083.2]

/-- Complete interval computation for depth 12, residue 1084. -/
theorem bounds_12_1084 : exactInterval 12 1084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1084 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1084) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1084 : oddCount 1084 12 = 5 ∧ acceleratedOrbit 12 1084 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1084 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1084) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1084.1, data_12_1084.2]

/-- Complete interval computation for depth 12, residue 1085. -/
theorem bounds_12_1085 : exactInterval 12 1085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1085 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1085) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1085 : oddCount 1085 12 = 5 ∧ acceleratedOrbit 12 1085 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1085 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1085) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1085.1, data_12_1085.2]

/-- Complete interval computation for depth 12, residue 1086. -/
theorem bounds_12_1086 : exactInterval 12 1086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1086 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1086) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1086 : oddCount 1086 12 = 7 ∧ acceleratedOrbit 12 1086 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1086 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1086) = 3 ^ 7 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1086.1, data_12_1086.2]

/-- Complete interval computation for depth 12, residue 1087. -/
theorem bounds_12_1087 : exactInterval 12 1087 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1087 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1087) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1087 : oddCount 1087 12 = 7 ∧ acceleratedOrbit 12 1087 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1087 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1087) = 3 ^ 7 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1087.1, data_12_1087.2]

/-- Complete interval computation for depth 12, residue 1088. -/
theorem bounds_12_1088 : exactInterval 12 1088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1088 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1088) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1088 : oddCount 1088 12 = 3 ∧ acceleratedOrbit 12 1088 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1088 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1088) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1088.1, data_12_1088.2]

/-- Complete interval computation for depth 12, residue 1089. -/
theorem bounds_12_1089 : exactInterval 12 1089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1089 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1089) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1089 : oddCount 1089 12 = 5 ∧ acceleratedOrbit 12 1089 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1089 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1089) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1089.1, data_12_1089.2]

end Collatz.Research.StoppingAtlas.Batch0271
