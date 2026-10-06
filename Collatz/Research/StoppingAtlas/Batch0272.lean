import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0272

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1090. -/
theorem bounds_12_1090 : exactInterval 12 1090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1090 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1090) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1090 : oddCount 1090 12 = 5 ∧ acceleratedOrbit 12 1090 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1090 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1090) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1090.1, data_12_1090.2]

/-- Complete interval computation for depth 12, residue 1091. -/
theorem bounds_12_1091 : exactInterval 12 1091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1091 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1091) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1091 : oddCount 1091 12 = 5 ∧ acceleratedOrbit 12 1091 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1091 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1091) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1091.1, data_12_1091.2]

/-- Complete interval computation for depth 12, residue 1092. -/
theorem bounds_12_1092 : exactInterval 12 1092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1092 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1092) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1092 : oddCount 1092 12 = 4 ∧ acceleratedOrbit 12 1092 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1092 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1092) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1092.1, data_12_1092.2]

/-- Complete interval computation for depth 12, residue 1093. -/
theorem bounds_12_1093 : exactInterval 12 1093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1093 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1093) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1093 : oddCount 1093 12 = 4 ∧ acceleratedOrbit 12 1093 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1093 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1093) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1093.1, data_12_1093.2]

/-- Complete interval computation for depth 12, residue 1094. -/
theorem bounds_12_1094 : exactInterval 12 1094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1094 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1094) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1094 : oddCount 1094 12 = 4 ∧ acceleratedOrbit 12 1094 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1094 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1094) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1094.1, data_12_1094.2]

/-- Complete interval computation for depth 12, residue 1095. -/
theorem bounds_12_1095 : exactInterval 12 1095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1095 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1095) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1095 : oddCount 1095 12 = 8 ∧ acceleratedOrbit 12 1095 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1095 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1095) = 3 ^ 8 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1095.1, data_12_1095.2]

/-- Complete interval computation for depth 12, residue 1096. -/
theorem bounds_12_1096 : exactInterval 12 1096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1096 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1096) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1096 : oddCount 1096 12 = 7 ∧ acceleratedOrbit 12 1096 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1096 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1096) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1096.1, data_12_1096.2]

/-- Complete interval computation for depth 12, residue 1097. -/
theorem bounds_12_1097 : exactInterval 12 1097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1097 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1097) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1097 : oddCount 1097 12 = 7 ∧ acceleratedOrbit 12 1097 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1097 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1097) = 3 ^ 7 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1097.1, data_12_1097.2]

/-- Complete interval computation for depth 12, residue 1098. -/
theorem bounds_12_1098 : exactInterval 12 1098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1098 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1098) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1098 : oddCount 1098 12 = 7 ∧ acceleratedOrbit 12 1098 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1098 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1098) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1098.1, data_12_1098.2]

/-- Complete interval computation for depth 12, residue 1099. -/
theorem bounds_12_1099 : exactInterval 12 1099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1099 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1099) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1099 : oddCount 1099 12 = 4 ∧ acceleratedOrbit 12 1099 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1099 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1099) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1099.1, data_12_1099.2]

/-- Complete interval computation for depth 12, residue 1100. -/
theorem bounds_12_1100 : exactInterval 12 1100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1100 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1100) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1100 : oddCount 1100 12 = 7 ∧ acceleratedOrbit 12 1100 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1100 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1100) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1100.1, data_12_1100.2]

/-- Complete interval computation for depth 12, residue 1101. -/
theorem bounds_12_1101 : exactInterval 12 1101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1101 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1101) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1101 : oddCount 1101 12 = 7 ∧ acceleratedOrbit 12 1101 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1101 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1101) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1101.1, data_12_1101.2]

/-- Complete interval computation for depth 12, residue 1102. -/
theorem bounds_12_1102 : exactInterval 12 1102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1102 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1102) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1102 : oddCount 1102 12 = 6 ∧ acceleratedOrbit 12 1102 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1102 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1102) = 3 ^ 6 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1102.1, data_12_1102.2]

/-- Complete interval computation for depth 12, residue 1103. -/
theorem bounds_12_1103 : exactInterval 12 1103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1103 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1103) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1103 : oddCount 1103 12 = 6 ∧ acceleratedOrbit 12 1103 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1103 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1103) = 3 ^ 6 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1103.1, data_12_1103.2]

/-- Complete interval computation for depth 12, residue 1104. -/
theorem bounds_12_1104 : exactInterval 12 1104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1104 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1104) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1104 : oddCount 1104 12 = 3 ∧ acceleratedOrbit 12 1104 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1104 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1104) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1104.1, data_12_1104.2]

end Collatz.Research.StoppingAtlas.Batch0272
