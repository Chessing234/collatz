import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0539

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1095. -/
theorem bounds_13_1095 : exactInterval 13 1095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1095 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1095) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1095 : oddCount 1095 13 = 9 ∧ acceleratedOrbit 13 1095 = 2636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1095 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1095) = 3 ^ 9 * m + 2636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1095.1, data_13_1095.2]

/-- Complete interval computation for depth 13, residue 1096. -/
theorem bounds_13_1096 : exactInterval 13 1096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1096 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1096) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1096 : oddCount 1096 13 = 8 ∧ acceleratedOrbit 13 1096 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1096 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1096) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1096.1, data_13_1096.2]

/-- Complete interval computation for depth 13, residue 1097. -/
theorem bounds_13_1097 : exactInterval 13 1097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1097 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1097) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1097 : oddCount 1097 13 = 8 ∧ acceleratedOrbit 13 1097 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1097 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1097) = 3 ^ 8 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1097.1, data_13_1097.2]

/-- Complete interval computation for depth 13, residue 1098. -/
theorem bounds_13_1098 : exactInterval 13 1098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1098 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1098) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1098 : oddCount 1098 13 = 8 ∧ acceleratedOrbit 13 1098 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1098 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1098) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1098.1, data_13_1098.2]

/-- Complete interval computation for depth 13, residue 1099. -/
theorem bounds_13_1099 : exactInterval 13 1099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1099 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1099) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1099 : oddCount 1099 13 = 4 ∧ acceleratedOrbit 13 1099 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1099 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1099) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1099.1, data_13_1099.2]

/-- Complete interval computation for depth 13, residue 1100. -/
theorem bounds_13_1100 : exactInterval 13 1100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1100 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1100) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1100 : oddCount 1100 13 = 8 ∧ acceleratedOrbit 13 1100 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1100 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1100) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1100.1, data_13_1100.2]

/-- Complete interval computation for depth 13, residue 1101. -/
theorem bounds_13_1101 : exactInterval 13 1101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1101 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1101) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1101 : oddCount 1101 13 = 8 ∧ acceleratedOrbit 13 1101 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1101 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1101) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1101.1, data_13_1101.2]

/-- Complete interval computation for depth 13, residue 1102. -/
theorem bounds_13_1102 : exactInterval 13 1102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1102 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1102) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1102 : oddCount 1102 13 = 7 ∧ acceleratedOrbit 13 1102 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1102 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1102) = 3 ^ 7 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1102.1, data_13_1102.2]

/-- Complete interval computation for depth 13, residue 1103. -/
theorem bounds_13_1103 : exactInterval 13 1103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1103 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1103) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1103 : oddCount 1103 13 = 7 ∧ acceleratedOrbit 13 1103 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1103 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1103) = 3 ^ 7 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1103.1, data_13_1103.2]

/-- Complete interval computation for depth 13, residue 1104. -/
theorem bounds_13_1104 : exactInterval 13 1104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1104 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1104) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1104 : oddCount 1104 13 = 3 ∧ acceleratedOrbit 13 1104 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1104 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1104) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1104.1, data_13_1104.2]

/-- Complete interval computation for depth 13, residue 1105. -/
theorem bounds_13_1105 : exactInterval 13 1105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1105 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1105) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1105 : oddCount 1105 13 = 8 ∧ acceleratedOrbit 13 1105 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1105 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1105) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1105.1, data_13_1105.2]

/-- Complete interval computation for depth 13, residue 1106. -/
theorem bounds_13_1106 : exactInterval 13 1106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1106 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1106) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1106 : oddCount 1106 13 = 9 ∧ acceleratedOrbit 13 1106 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1106 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1106) = 3 ^ 9 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1106.1, data_13_1106.2]

/-- Complete interval computation for depth 13, residue 1107. -/
theorem bounds_13_1107 : exactInterval 13 1107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1107 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1107) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1107 : oddCount 1107 13 = 9 ∧ acceleratedOrbit 13 1107 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1107 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1107) = 3 ^ 9 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1107.1, data_13_1107.2]

/-- Complete interval computation for depth 13, residue 1108. -/
theorem bounds_13_1108 : exactInterval 13 1108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1108 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1108) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1108 : oddCount 1108 13 = 3 ∧ acceleratedOrbit 13 1108 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1108 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1108) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1108.1, data_13_1108.2]

/-- Complete interval computation for depth 13, residue 1109. -/
theorem bounds_13_1109 : exactInterval 13 1109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1109 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1109) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1109 : oddCount 1109 13 = 3 ∧ acceleratedOrbit 13 1109 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1109 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1109) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1109.1, data_13_1109.2]

/-- Complete interval computation for depth 13, residue 1110. -/
theorem bounds_13_1110 : exactInterval 13 1110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1110 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1110) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1110 : oddCount 1110 13 = 4 ∧ acceleratedOrbit 13 1110 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1110 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1110) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1110.1, data_13_1110.2]

end Collatz.Research.StoppingAtlas.Batch0539
