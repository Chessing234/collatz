import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0143

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1157. -/
theorem bounds_11_1157 : exactInterval 11 1157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1157 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1157) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1157 : oddCount 1157 11 = 4 ∧ acceleratedOrbit 11 1157 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1157 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1157) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1157.1, data_11_1157.2]

/-- Complete interval computation for depth 11, residue 1158. -/
theorem bounds_11_1158 : exactInterval 11 1158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1158 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1158) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1158 : oddCount 1158 11 = 4 ∧ acceleratedOrbit 11 1158 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1158 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1158) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1158.1, data_11_1158.2]

/-- Complete interval computation for depth 11, residue 1159. -/
theorem bounds_11_1159 : exactInterval 11 1159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1159 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1159) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1159 : oddCount 1159 11 = 7 ∧ acceleratedOrbit 11 1159 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1159 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1159) = 3 ^ 7 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1159.1, data_11_1159.2]

/-- Complete interval computation for depth 11, residue 1160. -/
theorem bounds_11_1160 : exactInterval 11 1160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1160 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1160) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1160 : oddCount 1160 11 = 4 ∧ acceleratedOrbit 11 1160 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1160 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1160) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1160.1, data_11_1160.2]

/-- Complete interval computation for depth 11, residue 1161. -/
theorem bounds_11_1161 : exactInterval 11 1161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1161 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1161) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1161 : oddCount 1161 11 = 9 ∧ acceleratedOrbit 11 1161 = 11177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1161 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1161) = 3 ^ 9 * m + 11177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1161.1, data_11_1161.2]

/-- Complete interval computation for depth 11, residue 1162. -/
theorem bounds_11_1162 : exactInterval 11 1162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1162 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1162) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1162 : oddCount 1162 11 = 4 ∧ acceleratedOrbit 11 1162 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1162 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1162) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1162.1, data_11_1162.2]

/-- Complete interval computation for depth 11, residue 1163. -/
theorem bounds_11_1163 : exactInterval 11 1163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1163 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1163) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1163 : oddCount 1163 11 = 6 ∧ acceleratedOrbit 11 1163 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1163 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1163) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1163.1, data_11_1163.2]

/-- Complete interval computation for depth 11, residue 1164. -/
theorem bounds_11_1164 : exactInterval 11 1164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1164 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1164) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1164 : oddCount 1164 11 = 4 ∧ acceleratedOrbit 11 1164 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1164 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1164) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1164.1, data_11_1164.2]

/-- Complete interval computation for depth 11, residue 1165. -/
theorem bounds_11_1165 : exactInterval 11 1165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1165 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1165) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1165 : oddCount 1165 11 = 4 ∧ acceleratedOrbit 11 1165 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1165 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1165) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1165.1, data_11_1165.2]

/-- Complete interval computation for depth 11, residue 1166. -/
theorem bounds_11_1166 : exactInterval 11 1166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1166 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1166) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1166 : oddCount 1166 11 = 6 ∧ acceleratedOrbit 11 1166 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1166 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1166) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1166.1, data_11_1166.2]

/-- Complete interval computation for depth 11, residue 1167. -/
theorem bounds_11_1167 : exactInterval 11 1167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1167 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1167) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1167 : oddCount 1167 11 = 6 ∧ acceleratedOrbit 11 1167 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1167 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1167) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1167.1, data_11_1167.2]

/-- Complete interval computation for depth 11, residue 1168. -/
theorem bounds_11_1168 : exactInterval 11 1168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1168 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1168) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1168 : oddCount 1168 11 = 4 ∧ acceleratedOrbit 11 1168 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1168 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1168) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1168.1, data_11_1168.2]

/-- Complete interval computation for depth 11, residue 1169. -/
theorem bounds_11_1169 : exactInterval 11 1169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1169 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1169) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1169 : oddCount 1169 11 = 6 ∧ acceleratedOrbit 11 1169 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1169 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1169) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1169.1, data_11_1169.2]

/-- Complete interval computation for depth 11, residue 1170. -/
theorem bounds_11_1170 : exactInterval 11 1170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1170 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1170) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1170 : oddCount 1170 11 = 6 ∧ acceleratedOrbit 11 1170 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1170 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1170) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1170.1, data_11_1170.2]

/-- Complete interval computation for depth 11, residue 1171. -/
theorem bounds_11_1171 : exactInterval 11 1171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1171 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1171) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1171 : oddCount 1171 11 = 6 ∧ acceleratedOrbit 11 1171 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1171 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1171) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1171.1, data_11_1171.2]

end Collatz.Research.StoppingAtlas.Batch0143
