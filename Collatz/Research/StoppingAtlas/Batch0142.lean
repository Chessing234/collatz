import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0142

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1141. -/
theorem bounds_11_1141 : exactInterval 11 1141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1141 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1141) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1141 : oddCount 1141 11 = 5 ∧ acceleratedOrbit 11 1141 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1141 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1141) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1141.1, data_11_1141.2]

/-- Complete interval computation for depth 11, residue 1142. -/
theorem bounds_11_1142 : exactInterval 11 1142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1142 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1142) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1142 : oddCount 1142 11 = 5 ∧ acceleratedOrbit 11 1142 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1142 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1142) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1142.1, data_11_1142.2]

/-- Complete interval computation for depth 11, residue 1143. -/
theorem bounds_11_1143 : exactInterval 11 1143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1143 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1143) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1143 : oddCount 1143 11 = 5 ∧ acceleratedOrbit 11 1143 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1143 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1143) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1143.1, data_11_1143.2]

/-- Complete interval computation for depth 11, residue 1144. -/
theorem bounds_11_1144 : exactInterval 11 1144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1144 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1144) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1144 : oddCount 1144 11 = 5 ∧ acceleratedOrbit 11 1144 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1144 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1144) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1144.1, data_11_1144.2]

/-- Complete interval computation for depth 11, residue 1145. -/
theorem bounds_11_1145 : exactInterval 11 1145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1145 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1145) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1145 : oddCount 1145 11 = 7 ∧ acceleratedOrbit 11 1145 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1145 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1145) = 3 ^ 7 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1145.1, data_11_1145.2]

/-- Complete interval computation for depth 11, residue 1146. -/
theorem bounds_11_1146 : exactInterval 11 1146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1146 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1146) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1146 : oddCount 1146 11 = 5 ∧ acceleratedOrbit 11 1146 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1146 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1146) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1146.1, data_11_1146.2]

/-- Complete interval computation for depth 11, residue 1147. -/
theorem bounds_11_1147 : exactInterval 11 1147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1147 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1147) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1147 : oddCount 1147 11 = 6 ∧ acceleratedOrbit 11 1147 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1147 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1147) = 3 ^ 6 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1147.1, data_11_1147.2]

/-- Complete interval computation for depth 11, residue 1148. -/
theorem bounds_11_1148 : exactInterval 11 1148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1148 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1148) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1148 : oddCount 1148 11 = 6 ∧ acceleratedOrbit 11 1148 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1148 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1148) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1148.1, data_11_1148.2]

/-- Complete interval computation for depth 11, residue 1149. -/
theorem bounds_11_1149 : exactInterval 11 1149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1149 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1149) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1149 : oddCount 1149 11 = 6 ∧ acceleratedOrbit 11 1149 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1149 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1149) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1149.1, data_11_1149.2]

/-- Complete interval computation for depth 11, residue 1150. -/
theorem bounds_11_1150 : exactInterval 11 1150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1150 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1150) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1150 : oddCount 1150 11 = 6 ∧ acceleratedOrbit 11 1150 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1150 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1150) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1150.1, data_11_1150.2]

/-- Complete interval computation for depth 11, residue 1151. -/
theorem bounds_11_1151 : exactInterval 11 1151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1151 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1151) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1151 : oddCount 1151 11 = 9 ∧ acceleratedOrbit 11 1151 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1151 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1151) = 3 ^ 9 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1151.1, data_11_1151.2]

/-- Complete interval computation for depth 11, residue 1152. -/
theorem bounds_11_1152 : exactInterval 11 1152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1152 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1152) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1152 : oddCount 1152 11 = 3 ∧ acceleratedOrbit 11 1152 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1152 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1152) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1152.1, data_11_1152.2]

/-- Complete interval computation for depth 11, residue 1153. -/
theorem bounds_11_1153 : exactInterval 11 1153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1153 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1153) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1153 : oddCount 1153 11 = 7 ∧ acceleratedOrbit 11 1153 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1153 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1153) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1153.1, data_11_1153.2]

/-- Complete interval computation for depth 11, residue 1154. -/
theorem bounds_11_1154 : exactInterval 11 1154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1154 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1154) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1154 : oddCount 1154 11 = 4 ∧ acceleratedOrbit 11 1154 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1154 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1154) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1154.1, data_11_1154.2]

/-- Complete interval computation for depth 11, residue 1155. -/
theorem bounds_11_1155 : exactInterval 11 1155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1155 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1155) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1155 : oddCount 1155 11 = 4 ∧ acceleratedOrbit 11 1155 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1155 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1155) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1155.1, data_11_1155.2]

/-- Complete interval computation for depth 11, residue 1156. -/
theorem bounds_11_1156 : exactInterval 11 1156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1156 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1156) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1156 : oddCount 1156 11 = 4 ∧ acceleratedOrbit 11 1156 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1156 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1156) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1156.1, data_11_1156.2]

end Collatz.Research.StoppingAtlas.Batch0142
