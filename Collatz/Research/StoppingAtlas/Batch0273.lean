import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0273

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1105. -/
theorem bounds_12_1105 : exactInterval 12 1105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1105 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1105) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1105 : oddCount 1105 12 = 7 ∧ acceleratedOrbit 12 1105 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1105 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1105) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1105.1, data_12_1105.2]

/-- Complete interval computation for depth 12, residue 1106. -/
theorem bounds_12_1106 : exactInterval 12 1106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1106 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1106) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1106 : oddCount 1106 12 = 8 ∧ acceleratedOrbit 12 1106 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1106 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1106) = 3 ^ 8 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1106.1, data_12_1106.2]

/-- Complete interval computation for depth 12, residue 1107. -/
theorem bounds_12_1107 : exactInterval 12 1107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1107 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1107) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1107 : oddCount 1107 12 = 8 ∧ acceleratedOrbit 12 1107 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1107 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1107) = 3 ^ 8 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1107.1, data_12_1107.2]

/-- Complete interval computation for depth 12, residue 1108. -/
theorem bounds_12_1108 : exactInterval 12 1108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1108 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1108) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1108 : oddCount 1108 12 = 3 ∧ acceleratedOrbit 12 1108 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1108 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1108) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1108.1, data_12_1108.2]

/-- Complete interval computation for depth 12, residue 1109. -/
theorem bounds_12_1109 : exactInterval 12 1109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1109 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1109) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1109 : oddCount 1109 12 = 3 ∧ acceleratedOrbit 12 1109 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1109 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1109) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1109.1, data_12_1109.2]

/-- Complete interval computation for depth 12, residue 1110. -/
theorem bounds_12_1110 : exactInterval 12 1110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1110 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1110) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1110 : oddCount 1110 12 = 4 ∧ acceleratedOrbit 12 1110 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1110 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1110) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1110.1, data_12_1110.2]

/-- Complete interval computation for depth 12, residue 1111. -/
theorem bounds_12_1111 : exactInterval 12 1111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1111 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1111) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1111 : oddCount 1111 12 = 4 ∧ acceleratedOrbit 12 1111 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1111 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1111) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1111.1, data_12_1111.2]

/-- Complete interval computation for depth 12, residue 1112. -/
theorem bounds_12_1112 : exactInterval 12 1112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1112 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1112) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1112 : oddCount 1112 12 = 5 ∧ acceleratedOrbit 12 1112 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1112 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1112) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1112.1, data_12_1112.2]

/-- Complete interval computation for depth 12, residue 1113. -/
theorem bounds_12_1113 : exactInterval 12 1113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1113 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1113) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1113 : oddCount 1113 12 = 6 ∧ acceleratedOrbit 12 1113 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1113 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1113) = 3 ^ 6 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1113.1, data_12_1113.2]

/-- Complete interval computation for depth 12, residue 1114. -/
theorem bounds_12_1114 : exactInterval 12 1114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1114 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1114) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1114 : oddCount 1114 12 = 5 ∧ acceleratedOrbit 12 1114 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1114 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1114) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1114.1, data_12_1114.2]

/-- Complete interval computation for depth 12, residue 1115. -/
theorem bounds_12_1115 : exactInterval 12 1115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1115 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1115) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1115 : oddCount 1115 12 = 9 ∧ acceleratedOrbit 12 1115 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1115 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1115) = 3 ^ 9 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1115.1, data_12_1115.2]

/-- Complete interval computation for depth 12, residue 1116. -/
theorem bounds_12_1116 : exactInterval 12 1116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1116 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1116) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1116 : oddCount 1116 12 = 5 ∧ acceleratedOrbit 12 1116 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1116 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1116) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1116.1, data_12_1116.2]

/-- Complete interval computation for depth 12, residue 1117. -/
theorem bounds_12_1117 : exactInterval 12 1117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1117 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1117) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1117 : oddCount 1117 12 = 5 ∧ acceleratedOrbit 12 1117 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1117 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1117) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1117.1, data_12_1117.2]

/-- Complete interval computation for depth 12, residue 1118. -/
theorem bounds_12_1118 : exactInterval 12 1118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1118 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1118) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1118 : oddCount 1118 12 = 8 ∧ acceleratedOrbit 12 1118 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1118 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1118) = 3 ^ 8 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1118.1, data_12_1118.2]

/-- Complete interval computation for depth 12, residue 1119. -/
theorem bounds_12_1119 : exactInterval 12 1119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1119 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1119) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1119 : oddCount 1119 12 = 8 ∧ acceleratedOrbit 12 1119 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1119 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1119) = 3 ^ 8 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1119.1, data_12_1119.2]

/-- Complete interval computation for depth 12, residue 1120. -/
theorem bounds_12_1120 : exactInterval 12 1120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1120 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1120) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1120 : oddCount 1120 12 = 3 ∧ acceleratedOrbit 12 1120 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1120 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1120) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1120.1, data_12_1120.2]

end Collatz.Research.StoppingAtlas.Batch0273
