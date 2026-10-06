import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0036

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1146. -/
theorem bounds_15_1146 : exactInterval 15 1146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1146 : oddCount 1146 15 = 8 ∧ acceleratedOrbit 15 1146 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1146) = 3 ^ 8 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1146.1, data_15_1146.2]

/-- Complete interval computation for depth 15, residue 1147. -/
theorem bounds_15_1147 : exactInterval 15 1147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1147 : oddCount 1147 15 = 9 ∧ acceleratedOrbit 15 1147 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1147) = 3 ^ 9 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1147.1, data_15_1147.2]

/-- Complete interval computation for depth 15, residue 1148. -/
theorem bounds_15_1148 : exactInterval 15 1148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1148 : oddCount 1148 15 = 7 ∧ acceleratedOrbit 15 1148 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1148) = 3 ^ 7 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1148.1, data_15_1148.2]

/-- Complete interval computation for depth 15, residue 1149. -/
theorem bounds_15_1149 : exactInterval 15 1149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1149 : oddCount 1149 15 = 7 ∧ acceleratedOrbit 15 1149 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1149) = 3 ^ 7 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1149.1, data_15_1149.2]

/-- Complete interval computation for depth 15, residue 1150. -/
theorem bounds_15_1150 : exactInterval 15 1150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1150 : oddCount 1150 15 = 7 ∧ acceleratedOrbit 15 1150 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1150) = 3 ^ 7 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1150.1, data_15_1150.2]

/-- Complete interval computation for depth 15, residue 1151. -/
theorem bounds_15_1151 : exactInterval 15 1151 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1151) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1151 : oddCount 1151 15 = 9 ∧ acceleratedOrbit 15 1151 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1151) = 3 ^ 9 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1151.1, data_15_1151.2]

/-- Complete interval computation for depth 15, residue 1152. -/
theorem bounds_15_1152 : exactInterval 15 1152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1152 : oddCount 1152 15 = 5 ∧ acceleratedOrbit 15 1152 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1152) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1152.1, data_15_1152.2]

/-- Complete interval computation for depth 15, residue 1153. -/
theorem bounds_15_1153 : exactInterval 15 1153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1153 : oddCount 1153 15 = 9 ∧ acceleratedOrbit 15 1153 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1153) = 3 ^ 9 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1153.1, data_15_1153.2]

/-- Complete interval computation for depth 15, residue 1154. -/
theorem bounds_15_1154 : exactInterval 15 1154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1154 : oddCount 1154 15 = 7 ∧ acceleratedOrbit 15 1154 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1154) = 3 ^ 7 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1154.1, data_15_1154.2]

/-- Complete interval computation for depth 15, residue 1155. -/
theorem bounds_15_1155 : exactInterval 15 1155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1155 : oddCount 1155 15 = 7 ∧ acceleratedOrbit 15 1155 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1155) = 3 ^ 7 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1155.1, data_15_1155.2]

/-- Complete interval computation for depth 15, residue 1156. -/
theorem bounds_15_1156 : exactInterval 15 1156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1156 : oddCount 1156 15 = 7 ∧ acceleratedOrbit 15 1156 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1156) = 3 ^ 7 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1156.1, data_15_1156.2]

/-- Complete interval computation for depth 15, residue 1157. -/
theorem bounds_15_1157 : exactInterval 15 1157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1157 : oddCount 1157 15 = 7 ∧ acceleratedOrbit 15 1157 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1157) = 3 ^ 7 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1157.1, data_15_1157.2]

/-- Complete interval computation for depth 15, residue 1158. -/
theorem bounds_15_1158 : exactInterval 15 1158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1158 : oddCount 1158 15 = 7 ∧ acceleratedOrbit 15 1158 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1158) = 3 ^ 7 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1158.1, data_15_1158.2]

/-- Complete interval computation for depth 15, residue 1159. -/
theorem bounds_15_1159 : exactInterval 15 1159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1159 : oddCount 1159 15 = 10 ∧ acceleratedOrbit 15 1159 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1159) = 3 ^ 10 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1159.1, data_15_1159.2]

/-- Complete interval computation for depth 15, residue 1160. -/
theorem bounds_15_1160 : exactInterval 15 1160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1160 : oddCount 1160 15 = 8 ∧ acceleratedOrbit 15 1160 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1160) = 3 ^ 8 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1160.1, data_15_1160.2]

/-- Complete interval computation for depth 15, residue 1161. -/
theorem bounds_15_1161 : exactInterval 15 1161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1161 : oddCount 1161 15 = 12 ∧ acceleratedOrbit 15 1161 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1161) = 3 ^ 12 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1161.1, data_15_1161.2]

/-- Complete interval computation for depth 15, residue 1162. -/
theorem bounds_15_1162 : exactInterval 15 1162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1162 : oddCount 1162 15 = 8 ∧ acceleratedOrbit 15 1162 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1162) = 3 ^ 8 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1162.1, data_15_1162.2]

/-- Complete interval computation for depth 15, residue 1163. -/
theorem bounds_15_1163 : exactInterval 15 1163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1163 : oddCount 1163 15 = 10 ∧ acceleratedOrbit 15 1163 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1163) = 3 ^ 10 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1163.1, data_15_1163.2]

/-- Complete interval computation for depth 15, residue 1164. -/
theorem bounds_15_1164 : exactInterval 15 1164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1164 : oddCount 1164 15 = 8 ∧ acceleratedOrbit 15 1164 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1164) = 3 ^ 8 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1164.1, data_15_1164.2]

/-- Complete interval computation for depth 15, residue 1165. -/
theorem bounds_15_1165 : exactInterval 15 1165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1165 : oddCount 1165 15 = 8 ∧ acceleratedOrbit 15 1165 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1165) = 3 ^ 8 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1165.1, data_15_1165.2]

/-- Complete interval computation for depth 15, residue 1166. -/
theorem bounds_15_1166 : exactInterval 15 1166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1166 : oddCount 1166 15 = 6 ∧ acceleratedOrbit 15 1166 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1166) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1166.1, data_15_1166.2]

/-- Complete interval computation for depth 15, residue 1167. -/
theorem bounds_15_1167 : exactInterval 15 1167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1167 : oddCount 1167 15 = 6 ∧ acceleratedOrbit 15 1167 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1167) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1167.1, data_15_1167.2]

/-- Complete interval computation for depth 15, residue 1168. -/
theorem bounds_15_1168 : exactInterval 15 1168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1168 : oddCount 1168 15 = 8 ∧ acceleratedOrbit 15 1168 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1168) = 3 ^ 8 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1168.1, data_15_1168.2]

/-- Complete interval computation for depth 15, residue 1169. -/
theorem bounds_15_1169 : exactInterval 15 1169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1169 : oddCount 1169 15 = 8 ∧ acceleratedOrbit 15 1169 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1169) = 3 ^ 8 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1169.1, data_15_1169.2]

/-- Complete interval computation for depth 15, residue 1170. -/
theorem bounds_15_1170 : exactInterval 15 1170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1170 : oddCount 1170 15 = 8 ∧ acceleratedOrbit 15 1170 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1170) = 3 ^ 8 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1170.1, data_15_1170.2]

/-- Complete interval computation for depth 15, residue 1171. -/
theorem bounds_15_1171 : exactInterval 15 1171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1171 : oddCount 1171 15 = 8 ∧ acceleratedOrbit 15 1171 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1171) = 3 ^ 8 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1171.1, data_15_1171.2]

/-- Complete interval computation for depth 15, residue 1172. -/
theorem bounds_15_1172 : exactInterval 15 1172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1172 : oddCount 1172 15 = 8 ∧ acceleratedOrbit 15 1172 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1172) = 3 ^ 8 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1172.1, data_15_1172.2]

/-- Complete interval computation for depth 15, residue 1173. -/
theorem bounds_15_1173 : exactInterval 15 1173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1173 : oddCount 1173 15 = 8 ∧ acceleratedOrbit 15 1173 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1173) = 3 ^ 8 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1173.1, data_15_1173.2]

/-- Complete interval computation for depth 15, residue 1174. -/
theorem bounds_15_1174 : exactInterval 15 1174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1174 : oddCount 1174 15 = 8 ∧ acceleratedOrbit 15 1174 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1174) = 3 ^ 8 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1174.1, data_15_1174.2]

/-- Complete interval computation for depth 15, residue 1175. -/
theorem bounds_15_1175 : exactInterval 15 1175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1175 : oddCount 1175 15 = 8 ∧ acceleratedOrbit 15 1175 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1175) = 3 ^ 8 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1175.1, data_15_1175.2]

/-- Complete interval computation for depth 15, residue 1176. -/
theorem bounds_15_1176 : exactInterval 15 1176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1176 : oddCount 1176 15 = 8 ∧ acceleratedOrbit 15 1176 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1176) = 3 ^ 8 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1176.1, data_15_1176.2]

/-- Complete interval computation for depth 15, residue 1177. -/
theorem bounds_15_1177 : exactInterval 15 1177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1177 : oddCount 1177 15 = 7 ∧ acceleratedOrbit 15 1177 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1177) = 3 ^ 7 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1177.1, data_15_1177.2]

/-- Complete interval computation for depth 15, residue 1178. -/
theorem bounds_15_1178 : exactInterval 15 1178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1178 : oddCount 1178 15 = 8 ∧ acceleratedOrbit 15 1178 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1178) = 3 ^ 8 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1178.1, data_15_1178.2]

end Collatz.Research.PassageAtlas.Batch0036
