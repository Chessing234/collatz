import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0139

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1095. -/
theorem bounds_11_1095 : exactInterval 11 1095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1095 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1095) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1095 : oddCount 1095 11 = 7 ∧ acceleratedOrbit 11 1095 = 1171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1095 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1095) = 3 ^ 7 * m + 1171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1095.1, data_11_1095.2]

/-- Complete interval computation for depth 11, residue 1096. -/
theorem bounds_11_1096 : exactInterval 11 1096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1096 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1096) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1096 : oddCount 1096 11 = 6 ∧ acceleratedOrbit 11 1096 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1096 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1096) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1096.1, data_11_1096.2]

/-- Complete interval computation for depth 11, residue 1097. -/
theorem bounds_11_1097 : exactInterval 11 1097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1097 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1097) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1097 : oddCount 1097 11 = 7 ∧ acceleratedOrbit 11 1097 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1097 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1097) = 3 ^ 7 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1097.1, data_11_1097.2]

/-- Complete interval computation for depth 11, residue 1098. -/
theorem bounds_11_1098 : exactInterval 11 1098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1098 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1098) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1098 : oddCount 1098 11 = 6 ∧ acceleratedOrbit 11 1098 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1098 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1098) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1098.1, data_11_1098.2]

/-- Complete interval computation for depth 11, residue 1099. -/
theorem bounds_11_1099 : exactInterval 11 1099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1099 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1099) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1099 : oddCount 1099 11 = 4 ∧ acceleratedOrbit 11 1099 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1099 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1099) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1099.1, data_11_1099.2]

/-- Complete interval computation for depth 11, residue 1100. -/
theorem bounds_11_1100 : exactInterval 11 1100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1100 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1100) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1100 : oddCount 1100 11 = 6 ∧ acceleratedOrbit 11 1100 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1100 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1100) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1100.1, data_11_1100.2]

/-- Complete interval computation for depth 11, residue 1101. -/
theorem bounds_11_1101 : exactInterval 11 1101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1101 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1101) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1101 : oddCount 1101 11 = 6 ∧ acceleratedOrbit 11 1101 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1101 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1101) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1101.1, data_11_1101.2]

/-- Complete interval computation for depth 11, residue 1102. -/
theorem bounds_11_1102 : exactInterval 11 1102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1102 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1102) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1102 : oddCount 1102 11 = 5 ∧ acceleratedOrbit 11 1102 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1102 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1102) = 3 ^ 5 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1102.1, data_11_1102.2]

/-- Complete interval computation for depth 11, residue 1103. -/
theorem bounds_11_1103 : exactInterval 11 1103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1103 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1103) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1103 : oddCount 1103 11 = 5 ∧ acceleratedOrbit 11 1103 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1103 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1103) = 3 ^ 5 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1103.1, data_11_1103.2]

/-- Complete interval computation for depth 11, residue 1104. -/
theorem bounds_11_1104 : exactInterval 11 1104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1104 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1104) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1104 : oddCount 1104 11 = 2 ∧ acceleratedOrbit 11 1104 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1104 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1104) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1104.1, data_11_1104.2]

/-- Complete interval computation for depth 11, residue 1105. -/
theorem bounds_11_1105 : exactInterval 11 1105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1105 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1105) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1105 : oddCount 1105 11 = 6 ∧ acceleratedOrbit 11 1105 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1105 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1105) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1105.1, data_11_1105.2]

/-- Complete interval computation for depth 11, residue 1106. -/
theorem bounds_11_1106 : exactInterval 11 1106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1106 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1106) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1106 : oddCount 1106 11 = 8 ∧ acceleratedOrbit 11 1106 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1106 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1106) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1106.1, data_11_1106.2]

/-- Complete interval computation for depth 11, residue 1107. -/
theorem bounds_11_1107 : exactInterval 11 1107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1107 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1107) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1107 : oddCount 1107 11 = 8 ∧ acceleratedOrbit 11 1107 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1107 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1107) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1107.1, data_11_1107.2]

/-- Complete interval computation for depth 11, residue 1108. -/
theorem bounds_11_1108 : exactInterval 11 1108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1108 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1108) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1108 : oddCount 1108 11 = 2 ∧ acceleratedOrbit 11 1108 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1108 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1108) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1108.1, data_11_1108.2]

/-- Complete interval computation for depth 11, residue 1109. -/
theorem bounds_11_1109 : exactInterval 11 1109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1109 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1109) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1109 : oddCount 1109 11 = 2 ∧ acceleratedOrbit 11 1109 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1109 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1109) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1109.1, data_11_1109.2]

/-- Complete interval computation for depth 11, residue 1110. -/
theorem bounds_11_1110 : exactInterval 11 1110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1110 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1110) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1110 : oddCount 1110 11 = 4 ∧ acceleratedOrbit 11 1110 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1110 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1110) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1110.1, data_11_1110.2]

end Collatz.Research.StoppingAtlas.Batch0139
