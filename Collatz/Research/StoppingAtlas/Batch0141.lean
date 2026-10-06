import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0141

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1126. -/
theorem bounds_11_1126 : exactInterval 11 1126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1126 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1126) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1126 : oddCount 1126 11 = 6 ∧ acceleratedOrbit 11 1126 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1126 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1126) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1126.1, data_11_1126.2]

/-- Complete interval computation for depth 11, residue 1127. -/
theorem bounds_11_1127 : exactInterval 11 1127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1127 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1127) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1127 : oddCount 1127 11 = 9 ∧ acceleratedOrbit 11 1127 = 10844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1127 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1127) = 3 ^ 9 * m + 10844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1127.1, data_11_1127.2]

/-- Complete interval computation for depth 11, residue 1128. -/
theorem bounds_11_1128 : exactInterval 11 1128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1128 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1128) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1128 : oddCount 1128 11 = 2 ∧ acceleratedOrbit 11 1128 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1128 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1128) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1128.1, data_11_1128.2]

/-- Complete interval computation for depth 11, residue 1129. -/
theorem bounds_11_1129 : exactInterval 11 1129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1129 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1129) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1129 : oddCount 1129 11 = 7 ∧ acceleratedOrbit 11 1129 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1129 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1129) = 3 ^ 7 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1129.1, data_11_1129.2]

/-- Complete interval computation for depth 11, residue 1130. -/
theorem bounds_11_1130 : exactInterval 11 1130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1130 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1130) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1130 : oddCount 1130 11 = 2 ∧ acceleratedOrbit 11 1130 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1130 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1130) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1130.1, data_11_1130.2]

/-- Complete interval computation for depth 11, residue 1131. -/
theorem bounds_11_1131 : exactInterval 11 1131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1131 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1131) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1131 : oddCount 1131 11 = 7 ∧ acceleratedOrbit 11 1131 = 1210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1131 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1131) = 3 ^ 7 * m + 1210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1131.1, data_11_1131.2]

/-- Complete interval computation for depth 11, residue 1132. -/
theorem bounds_11_1132 : exactInterval 11 1132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1132 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1132) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1132 : oddCount 1132 11 = 8 ∧ acceleratedOrbit 11 1132 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1132 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1132) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1132.1, data_11_1132.2]

/-- Complete interval computation for depth 11, residue 1133. -/
theorem bounds_11_1133 : exactInterval 11 1133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1133 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1133) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1133 : oddCount 1133 11 = 8 ∧ acceleratedOrbit 11 1133 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1133 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1133) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1133.1, data_11_1133.2]

/-- Complete interval computation for depth 11, residue 1134. -/
theorem bounds_11_1134 : exactInterval 11 1134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1134 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1134) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1134 : oddCount 1134 11 = 8 ∧ acceleratedOrbit 11 1134 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1134 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1134) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1134.1, data_11_1134.2]

/-- Complete interval computation for depth 11, residue 1135. -/
theorem bounds_11_1135 : exactInterval 11 1135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1135 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1135) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1135 : oddCount 1135 11 = 8 ∧ acceleratedOrbit 11 1135 = 3640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1135 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1135) = 3 ^ 8 * m + 3640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1135.1, data_11_1135.2]

/-- Complete interval computation for depth 11, residue 1136. -/
theorem bounds_11_1136 : exactInterval 11 1136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1136 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1136) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1136 : oddCount 1136 11 = 5 ∧ acceleratedOrbit 11 1136 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1136 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1136) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1136.1, data_11_1136.2]

/-- Complete interval computation for depth 11, residue 1137. -/
theorem bounds_11_1137 : exactInterval 11 1137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1137 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1137) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1137 : oddCount 1137 11 = 2 ∧ acceleratedOrbit 11 1137 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1137 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1137) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1137.1, data_11_1137.2]

/-- Complete interval computation for depth 11, residue 1138. -/
theorem bounds_11_1138 : exactInterval 11 1138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1138 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1138) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1138 : oddCount 1138 11 = 6 ∧ acceleratedOrbit 11 1138 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1138 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1138) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1138.1, data_11_1138.2]

/-- Complete interval computation for depth 11, residue 1139. -/
theorem bounds_11_1139 : exactInterval 11 1139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1139 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1139) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1139 : oddCount 1139 11 = 6 ∧ acceleratedOrbit 11 1139 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1139 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1139) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1139.1, data_11_1139.2]

/-- Complete interval computation for depth 11, residue 1140. -/
theorem bounds_11_1140 : exactInterval 11 1140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1140 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1140) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1140 : oddCount 1140 11 = 5 ∧ acceleratedOrbit 11 1140 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1140 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1140) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1140.1, data_11_1140.2]

end Collatz.Research.StoppingAtlas.Batch0141
