import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0541

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1126. -/
theorem bounds_13_1126 : exactInterval 13 1126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1126 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1126) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1126 : oddCount 1126 13 = 6 ∧ acceleratedOrbit 13 1126 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1126 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1126) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1126.1, data_13_1126.2]

/-- Complete interval computation for depth 13, residue 1127. -/
theorem bounds_13_1127 : exactInterval 13 1127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1127 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1127) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1127 : oddCount 1127 13 = 9 ∧ acceleratedOrbit 13 1127 = 2711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1127 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1127) = 3 ^ 9 * m + 2711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1127.1, data_13_1127.2]

/-- Complete interval computation for depth 13, residue 1128. -/
theorem bounds_13_1128 : exactInterval 13 1128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1128 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1128) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1128 : oddCount 1128 13 = 3 ∧ acceleratedOrbit 13 1128 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1128 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1128) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1128.1, data_13_1128.2]

/-- Complete interval computation for depth 13, residue 1129. -/
theorem bounds_13_1129 : exactInterval 13 1129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1129 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1129) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1129 : oddCount 1129 13 = 7 ∧ acceleratedOrbit 13 1129 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1129 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1129) = 3 ^ 7 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1129.1, data_13_1129.2]

/-- Complete interval computation for depth 13, residue 1130. -/
theorem bounds_13_1130 : exactInterval 13 1130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1130 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1130) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1130 : oddCount 1130 13 = 3 ∧ acceleratedOrbit 13 1130 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1130 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1130) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1130.1, data_13_1130.2]

/-- Complete interval computation for depth 13, residue 1131. -/
theorem bounds_13_1131 : exactInterval 13 1131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1131 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1131) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1131 : oddCount 1131 13 = 8 ∧ acceleratedOrbit 13 1131 = 908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1131 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1131) = 3 ^ 8 * m + 908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1131.1, data_13_1131.2]

/-- Complete interval computation for depth 13, residue 1132. -/
theorem bounds_13_1132 : exactInterval 13 1132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1132 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1132) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1132 : oddCount 1132 13 = 8 ∧ acceleratedOrbit 13 1132 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1132 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1132) = 3 ^ 8 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1132.1, data_13_1132.2]

/-- Complete interval computation for depth 13, residue 1133. -/
theorem bounds_13_1133 : exactInterval 13 1133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1133 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1133) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1133 : oddCount 1133 13 = 8 ∧ acceleratedOrbit 13 1133 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1133 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1133) = 3 ^ 8 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1133.1, data_13_1133.2]

/-- Complete interval computation for depth 13, residue 1134. -/
theorem bounds_13_1134 : exactInterval 13 1134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1134 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1134) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1134 : oddCount 1134 13 = 8 ∧ acceleratedOrbit 13 1134 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1134 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1134) = 3 ^ 8 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1134.1, data_13_1134.2]

/-- Complete interval computation for depth 13, residue 1135. -/
theorem bounds_13_1135 : exactInterval 13 1135 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1135 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1135) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1135 : oddCount 1135 13 = 8 ∧ acceleratedOrbit 13 1135 = 910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1135 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1135) = 3 ^ 8 * m + 910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1135.1, data_13_1135.2]

/-- Complete interval computation for depth 13, residue 1136. -/
theorem bounds_13_1136 : exactInterval 13 1136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1136 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1136) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1136 : oddCount 1136 13 = 6 ∧ acceleratedOrbit 13 1136 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1136 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1136) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1136.1, data_13_1136.2]

/-- Complete interval computation for depth 13, residue 1137. -/
theorem bounds_13_1137 : exactInterval 13 1137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1137 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1137) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1137 : oddCount 1137 13 = 3 ∧ acceleratedOrbit 13 1137 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1137 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1137) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1137.1, data_13_1137.2]

/-- Complete interval computation for depth 13, residue 1138. -/
theorem bounds_13_1138 : exactInterval 13 1138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1138 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1138) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1138 : oddCount 1138 13 = 8 ∧ acceleratedOrbit 13 1138 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1138 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1138) = 3 ^ 8 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1138.1, data_13_1138.2]

/-- Complete interval computation for depth 13, residue 1139. -/
theorem bounds_13_1139 : exactInterval 13 1139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1139 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1139) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1139 : oddCount 1139 13 = 8 ∧ acceleratedOrbit 13 1139 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1139 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1139) = 3 ^ 8 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1139.1, data_13_1139.2]

/-- Complete interval computation for depth 13, residue 1140. -/
theorem bounds_13_1140 : exactInterval 13 1140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1140 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1140) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1140 : oddCount 1140 13 = 6 ∧ acceleratedOrbit 13 1140 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1140 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1140) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1140.1, data_13_1140.2]

end Collatz.Research.StoppingAtlas.Batch0541
