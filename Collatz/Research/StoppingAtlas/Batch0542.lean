import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0542

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1141. -/
theorem bounds_13_1141 : exactInterval 13 1141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1141 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1141) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1141 : oddCount 1141 13 = 6 ∧ acceleratedOrbit 13 1141 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1141 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1141) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1141.1, data_13_1141.2]

/-- Complete interval computation for depth 13, residue 1142. -/
theorem bounds_13_1142 : exactInterval 13 1142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1142 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1142) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1142 : oddCount 1142 13 = 5 ∧ acceleratedOrbit 13 1142 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1142 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1142) = 3 ^ 5 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1142.1, data_13_1142.2]

/-- Complete interval computation for depth 13, residue 1143. -/
theorem bounds_13_1143 : exactInterval 13 1143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1143 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1143) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1143 : oddCount 1143 13 = 5 ∧ acceleratedOrbit 13 1143 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1143 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1143) = 3 ^ 5 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1143.1, data_13_1143.2]

/-- Complete interval computation for depth 13, residue 1144. -/
theorem bounds_13_1144 : exactInterval 13 1144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1144 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1144) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1144 : oddCount 1144 13 = 6 ∧ acceleratedOrbit 13 1144 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1144 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1144) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1144.1, data_13_1144.2]

/-- Complete interval computation for depth 13, residue 1145. -/
theorem bounds_13_1145 : exactInterval 13 1145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1145 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1145) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1145 : oddCount 1145 13 = 8 ∧ acceleratedOrbit 13 1145 = 919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1145 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1145) = 3 ^ 8 * m + 919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1145.1, data_13_1145.2]

/-- Complete interval computation for depth 13, residue 1146. -/
theorem bounds_13_1146 : exactInterval 13 1146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1146 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1146) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1146 : oddCount 1146 13 = 6 ∧ acceleratedOrbit 13 1146 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1146 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1146) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1146.1, data_13_1146.2]

/-- Complete interval computation for depth 13, residue 1147. -/
theorem bounds_13_1147 : exactInterval 13 1147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1147 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1147) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1147 : oddCount 1147 13 = 7 ∧ acceleratedOrbit 13 1147 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1147 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1147) = 3 ^ 7 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1147.1, data_13_1147.2]

/-- Complete interval computation for depth 13, residue 1148. -/
theorem bounds_13_1148 : exactInterval 13 1148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1148 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1148) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1148 : oddCount 1148 13 = 7 ∧ acceleratedOrbit 13 1148 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1148 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1148) = 3 ^ 7 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1148.1, data_13_1148.2]

/-- Complete interval computation for depth 13, residue 1149. -/
theorem bounds_13_1149 : exactInterval 13 1149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1149 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1149) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1149 : oddCount 1149 13 = 7 ∧ acceleratedOrbit 13 1149 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1149 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1149) = 3 ^ 7 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1149.1, data_13_1149.2]

/-- Complete interval computation for depth 13, residue 1150. -/
theorem bounds_13_1150 : exactInterval 13 1150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1150 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1150) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1150 : oddCount 1150 13 = 7 ∧ acceleratedOrbit 13 1150 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1150 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1150) = 3 ^ 7 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1150.1, data_13_1150.2]

/-- Complete interval computation for depth 13, residue 1151. -/
theorem bounds_13_1151 : exactInterval 13 1151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1151 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1151) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1151 : oddCount 1151 13 = 9 ∧ acceleratedOrbit 13 1151 = 2768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1151 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1151) = 3 ^ 9 * m + 2768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1151.1, data_13_1151.2]

/-- Complete interval computation for depth 13, residue 1152. -/
theorem bounds_13_1152 : exactInterval 13 1152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1152 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1152) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1152 : oddCount 1152 13 = 4 ∧ acceleratedOrbit 13 1152 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1152 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1152) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1152.1, data_13_1152.2]

/-- Complete interval computation for depth 13, residue 1153. -/
theorem bounds_13_1153 : exactInterval 13 1153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1153 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1153) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1153 : oddCount 1153 13 = 9 ∧ acceleratedOrbit 13 1153 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1153 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1153) = 3 ^ 9 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1153.1, data_13_1153.2]

/-- Complete interval computation for depth 13, residue 1154. -/
theorem bounds_13_1154 : exactInterval 13 1154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1154 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1154) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1154 : oddCount 1154 13 = 5 ∧ acceleratedOrbit 13 1154 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1154 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1154) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1154.1, data_13_1154.2]

/-- Complete interval computation for depth 13, residue 1155. -/
theorem bounds_13_1155 : exactInterval 13 1155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1155 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1155) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1155 : oddCount 1155 13 = 5 ∧ acceleratedOrbit 13 1155 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1155 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1155) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1155.1, data_13_1155.2]

/-- Complete interval computation for depth 13, residue 1156. -/
theorem bounds_13_1156 : exactInterval 13 1156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1156 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1156) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1156 : oddCount 1156 13 = 5 ∧ acceleratedOrbit 13 1156 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1156 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1156) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1156.1, data_13_1156.2]

end Collatz.Research.StoppingAtlas.Batch0542
