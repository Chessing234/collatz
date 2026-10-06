import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0276

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1152. -/
theorem bounds_12_1152 : exactInterval 12 1152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1152 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1152) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1152 : oddCount 1152 12 = 4 ∧ acceleratedOrbit 12 1152 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1152 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1152) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1152.1, data_12_1152.2]

/-- Complete interval computation for depth 12, residue 1153. -/
theorem bounds_12_1153 : exactInterval 12 1153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1153 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1153) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1153 : oddCount 1153 12 = 8 ∧ acceleratedOrbit 12 1153 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1153 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1153) = 3 ^ 8 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1153.1, data_12_1153.2]

/-- Complete interval computation for depth 12, residue 1154. -/
theorem bounds_12_1154 : exactInterval 12 1154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1154 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1154) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1154 : oddCount 1154 12 = 4 ∧ acceleratedOrbit 12 1154 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1154 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1154) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1154.1, data_12_1154.2]

/-- Complete interval computation for depth 12, residue 1155. -/
theorem bounds_12_1155 : exactInterval 12 1155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1155 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1155) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1155 : oddCount 1155 12 = 4 ∧ acceleratedOrbit 12 1155 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1155 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1155) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1155.1, data_12_1155.2]

/-- Complete interval computation for depth 12, residue 1156. -/
theorem bounds_12_1156 : exactInterval 12 1156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1156 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1156) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1156 : oddCount 1156 12 = 4 ∧ acceleratedOrbit 12 1156 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1156 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1156) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1156.1, data_12_1156.2]

/-- Complete interval computation for depth 12, residue 1157. -/
theorem bounds_12_1157 : exactInterval 12 1157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1157 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1157) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1157 : oddCount 1157 12 = 4 ∧ acceleratedOrbit 12 1157 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1157 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1157) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1157.1, data_12_1157.2]

/-- Complete interval computation for depth 12, residue 1158. -/
theorem bounds_12_1158 : exactInterval 12 1158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1158 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1158) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1158 : oddCount 1158 12 = 4 ∧ acceleratedOrbit 12 1158 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1158 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1158) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1158.1, data_12_1158.2]

/-- Complete interval computation for depth 12, residue 1159. -/
theorem bounds_12_1159 : exactInterval 12 1159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1159 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1159) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1159 : oddCount 1159 12 = 8 ∧ acceleratedOrbit 12 1159 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1159 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1159) = 3 ^ 8 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1159.1, data_12_1159.2]

/-- Complete interval computation for depth 12, residue 1160. -/
theorem bounds_12_1160 : exactInterval 12 1160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1160 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1160) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1160 : oddCount 1160 12 = 5 ∧ acceleratedOrbit 12 1160 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1160 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1160) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1160.1, data_12_1160.2]

/-- Complete interval computation for depth 12, residue 1161. -/
theorem bounds_12_1161 : exactInterval 12 1161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1161 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1161) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1161 : oddCount 1161 12 = 10 ∧ acceleratedOrbit 12 1161 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1161 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1161) = 3 ^ 10 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1161.1, data_12_1161.2]

/-- Complete interval computation for depth 12, residue 1162. -/
theorem bounds_12_1162 : exactInterval 12 1162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1162 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1162) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1162 : oddCount 1162 12 = 5 ∧ acceleratedOrbit 12 1162 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1162 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1162) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1162.1, data_12_1162.2]

/-- Complete interval computation for depth 12, residue 1163. -/
theorem bounds_12_1163 : exactInterval 12 1163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1163 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1163) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1163 : oddCount 1163 12 = 7 ∧ acceleratedOrbit 12 1163 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1163 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1163) = 3 ^ 7 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1163.1, data_12_1163.2]

/-- Complete interval computation for depth 12, residue 1164. -/
theorem bounds_12_1164 : exactInterval 12 1164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1164 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1164) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1164 : oddCount 1164 12 = 5 ∧ acceleratedOrbit 12 1164 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1164 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1164) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1164.1, data_12_1164.2]

/-- Complete interval computation for depth 12, residue 1165. -/
theorem bounds_12_1165 : exactInterval 12 1165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1165 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1165) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1165 : oddCount 1165 12 = 5 ∧ acceleratedOrbit 12 1165 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1165 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1165) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1165.1, data_12_1165.2]

/-- Complete interval computation for depth 12, residue 1166. -/
theorem bounds_12_1166 : exactInterval 12 1166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1166 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1166) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1166 : oddCount 1166 12 = 6 ∧ acceleratedOrbit 12 1166 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1166 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1166) = 3 ^ 6 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1166.1, data_12_1166.2]

end Collatz.Research.StoppingAtlas.Batch0276
