import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0035

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1114. -/
theorem bounds_15_1114 : exactInterval 15 1114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1114 : oddCount 1114 15 = 7 ∧ acceleratedOrbit 15 1114 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1114) = 3 ^ 7 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1114.1, data_15_1114.2]

/-- Complete interval computation for depth 15, residue 1115. -/
theorem bounds_15_1115 : exactInterval 15 1115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1115 : oddCount 1115 15 = 11 ∧ acceleratedOrbit 15 1115 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1115) = 3 ^ 11 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1115.1, data_15_1115.2]

/-- Complete interval computation for depth 15, residue 1116. -/
theorem bounds_15_1116 : exactInterval 15 1116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1116 : oddCount 1116 15 = 7 ∧ acceleratedOrbit 15 1116 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1116) = 3 ^ 7 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1116.1, data_15_1116.2]

/-- Complete interval computation for depth 15, residue 1117. -/
theorem bounds_15_1117 : exactInterval 15 1117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1117 : oddCount 1117 15 = 7 ∧ acceleratedOrbit 15 1117 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1117) = 3 ^ 7 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1117.1, data_15_1117.2]

/-- Complete interval computation for depth 15, residue 1118. -/
theorem bounds_15_1118 : exactInterval 15 1118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1118 : oddCount 1118 15 = 10 ∧ acceleratedOrbit 15 1118 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1118) = 3 ^ 10 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1118.1, data_15_1118.2]

/-- Complete interval computation for depth 15, residue 1119. -/
theorem bounds_15_1119 : exactInterval 15 1119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1119 : oddCount 1119 15 = 10 ∧ acceleratedOrbit 15 1119 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1119) = 3 ^ 10 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1119.1, data_15_1119.2]

/-- Complete interval computation for depth 15, residue 1120. -/
theorem bounds_15_1120 : exactInterval 15 1120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1120 : oddCount 1120 15 = 3 ∧ acceleratedOrbit 15 1120 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1120) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1120.1, data_15_1120.2]

/-- Complete interval computation for depth 15, residue 1121. -/
theorem bounds_15_1121 : exactInterval 15 1121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1121 : oddCount 1121 15 = 6 ∧ acceleratedOrbit 15 1121 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1121) = 3 ^ 6 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1121.1, data_15_1121.2]

/-- Complete interval computation for depth 15, residue 1122. -/
theorem bounds_15_1122 : exactInterval 15 1122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1122 : oddCount 1122 15 = 7 ∧ acceleratedOrbit 15 1122 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1122) = 3 ^ 7 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1122.1, data_15_1122.2]

/-- Complete interval computation for depth 15, residue 1123. -/
theorem bounds_15_1123 : exactInterval 15 1123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1123 : oddCount 1123 15 = 7 ∧ acceleratedOrbit 15 1123 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1123) = 3 ^ 7 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1123.1, data_15_1123.2]

/-- Complete interval computation for depth 15, residue 1124. -/
theorem bounds_15_1124 : exactInterval 15 1124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1124 : oddCount 1124 15 = 7 ∧ acceleratedOrbit 15 1124 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1124) = 3 ^ 7 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1124.1, data_15_1124.2]

/-- Complete interval computation for depth 15, residue 1125. -/
theorem bounds_15_1125 : exactInterval 15 1125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1125 : oddCount 1125 15 = 7 ∧ acceleratedOrbit 15 1125 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1125) = 3 ^ 7 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1125.1, data_15_1125.2]

/-- Complete interval computation for depth 15, residue 1126. -/
theorem bounds_15_1126 : exactInterval 15 1126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1126 : oddCount 1126 15 = 7 ∧ acceleratedOrbit 15 1126 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1126) = 3 ^ 7 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1126.1, data_15_1126.2]

/-- Complete interval computation for depth 15, residue 1127. -/
theorem bounds_15_1127 : exactInterval 15 1127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1127 : oddCount 1127 15 = 11 ∧ acceleratedOrbit 15 1127 = 6101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1127) = 3 ^ 11 * m + 6101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1127.1, data_15_1127.2]

/-- Complete interval computation for depth 15, residue 1128. -/
theorem bounds_15_1128 : exactInterval 15 1128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1128 : oddCount 1128 15 = 3 ∧ acceleratedOrbit 15 1128 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1128) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1128.1, data_15_1128.2]

/-- Complete interval computation for depth 15, residue 1129. -/
theorem bounds_15_1129 : exactInterval 15 1129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1129 : oddCount 1129 15 = 8 ∧ acceleratedOrbit 15 1129 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1129) = 3 ^ 8 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1129.1, data_15_1129.2]

/-- Complete interval computation for depth 15, residue 1130. -/
theorem bounds_15_1130 : exactInterval 15 1130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1130 : oddCount 1130 15 = 3 ∧ acceleratedOrbit 15 1130 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1130) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1130.1, data_15_1130.2]

/-- Complete interval computation for depth 15, residue 1131. -/
theorem bounds_15_1131 : exactInterval 15 1131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1131 : oddCount 1131 15 = 8 ∧ acceleratedOrbit 15 1131 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1131) = 3 ^ 8 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1131.1, data_15_1131.2]

/-- Complete interval computation for depth 15, residue 1132. -/
theorem bounds_15_1132 : exactInterval 15 1132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1132 : oddCount 1132 15 = 10 ∧ acceleratedOrbit 15 1132 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1132) = 3 ^ 10 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1132.1, data_15_1132.2]

/-- Complete interval computation for depth 15, residue 1133. -/
theorem bounds_15_1133 : exactInterval 15 1133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1133 : oddCount 1133 15 = 10 ∧ acceleratedOrbit 15 1133 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1133) = 3 ^ 10 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1133.1, data_15_1133.2]

/-- Complete interval computation for depth 15, residue 1134. -/
theorem bounds_15_1134 : exactInterval 15 1134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1134 : oddCount 1134 15 = 10 ∧ acceleratedOrbit 15 1134 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1134) = 3 ^ 10 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1134.1, data_15_1134.2]

/-- Complete interval computation for depth 15, residue 1135. -/
theorem bounds_15_1135 : exactInterval 15 1135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1135 : oddCount 1135 15 = 9 ∧ acceleratedOrbit 15 1135 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1135) = 3 ^ 9 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1135.1, data_15_1135.2]

/-- Complete interval computation for depth 15, residue 1136. -/
theorem bounds_15_1136 : exactInterval 15 1136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1136 : oddCount 1136 15 = 8 ∧ acceleratedOrbit 15 1136 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1136) = 3 ^ 8 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1136.1, data_15_1136.2]

/-- Complete interval computation for depth 15, residue 1137. -/
theorem bounds_15_1137 : exactInterval 15 1137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1137 : oddCount 1137 15 = 3 ∧ acceleratedOrbit 15 1137 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1137) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1137.1, data_15_1137.2]

/-- Complete interval computation for depth 15, residue 1138. -/
theorem bounds_15_1138 : exactInterval 15 1138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1138 : oddCount 1138 15 = 9 ∧ acceleratedOrbit 15 1138 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1138) = 3 ^ 9 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1138.1, data_15_1138.2]

/-- Complete interval computation for depth 15, residue 1139. -/
theorem bounds_15_1139 : exactInterval 15 1139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1139 : oddCount 1139 15 = 9 ∧ acceleratedOrbit 15 1139 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1139) = 3 ^ 9 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1139.1, data_15_1139.2]

/-- Complete interval computation for depth 15, residue 1140. -/
theorem bounds_15_1140 : exactInterval 15 1140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1140 : oddCount 1140 15 = 8 ∧ acceleratedOrbit 15 1140 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1140) = 3 ^ 8 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1140.1, data_15_1140.2]

/-- Complete interval computation for depth 15, residue 1141. -/
theorem bounds_15_1141 : exactInterval 15 1141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1141 : oddCount 1141 15 = 8 ∧ acceleratedOrbit 15 1141 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1141) = 3 ^ 8 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1141.1, data_15_1141.2]

/-- Complete interval computation for depth 15, residue 1142. -/
theorem bounds_15_1142 : exactInterval 15 1142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1142 : oddCount 1142 15 = 6 ∧ acceleratedOrbit 15 1142 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1142) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1142.1, data_15_1142.2]

/-- Complete interval computation for depth 15, residue 1143. -/
theorem bounds_15_1143 : exactInterval 15 1143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1143 : oddCount 1143 15 = 6 ∧ acceleratedOrbit 15 1143 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1143) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1143.1, data_15_1143.2]

/-- Complete interval computation for depth 15, residue 1144. -/
theorem bounds_15_1144 : exactInterval 15 1144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1144 : oddCount 1144 15 = 8 ∧ acceleratedOrbit 15 1144 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1144) = 3 ^ 8 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1144.1, data_15_1144.2]

/-- Complete interval computation for depth 15, residue 1145. -/
theorem bounds_15_1145 : exactInterval 15 1145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1145 : oddCount 1145 15 = 10 ∧ acceleratedOrbit 15 1145 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1145) = 3 ^ 10 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1145.1, data_15_1145.2]

end Collatz.Research.PassageAtlas.Batch0035
