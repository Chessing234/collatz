import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0543

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1157. -/
theorem bounds_13_1157 : exactInterval 13 1157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1157 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1157) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1157 : oddCount 1157 13 = 5 ∧ acceleratedOrbit 13 1157 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1157 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1157) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1157.1, data_13_1157.2]

/-- Complete interval computation for depth 13, residue 1158. -/
theorem bounds_13_1158 : exactInterval 13 1158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1158 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1158) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1158 : oddCount 1158 13 = 5 ∧ acceleratedOrbit 13 1158 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1158 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1158) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1158.1, data_13_1158.2]

/-- Complete interval computation for depth 13, residue 1159. -/
theorem bounds_13_1159 : exactInterval 13 1159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1159 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1159) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1159 : oddCount 1159 13 = 8 ∧ acceleratedOrbit 13 1159 = 931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1159 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1159) = 3 ^ 8 * m + 931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1159.1, data_13_1159.2]

/-- Complete interval computation for depth 13, residue 1160. -/
theorem bounds_13_1160 : exactInterval 13 1160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1160 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1160) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1160 : oddCount 1160 13 = 6 ∧ acceleratedOrbit 13 1160 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1160 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1160) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1160.1, data_13_1160.2]

/-- Complete interval computation for depth 13, residue 1161. -/
theorem bounds_13_1161 : exactInterval 13 1161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1161 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1161) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1161 : oddCount 1161 13 = 10 ∧ acceleratedOrbit 13 1161 = 8383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1161 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1161) = 3 ^ 10 * m + 8383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1161.1, data_13_1161.2]

/-- Complete interval computation for depth 13, residue 1162. -/
theorem bounds_13_1162 : exactInterval 13 1162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1162 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1162) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1162 : oddCount 1162 13 = 6 ∧ acceleratedOrbit 13 1162 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1162 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1162) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1162.1, data_13_1162.2]

/-- Complete interval computation for depth 13, residue 1163. -/
theorem bounds_13_1163 : exactInterval 13 1163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1163 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1163) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1163 : oddCount 1163 13 = 8 ∧ acceleratedOrbit 13 1163 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1163 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1163) = 3 ^ 8 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1163.1, data_13_1163.2]

/-- Complete interval computation for depth 13, residue 1164. -/
theorem bounds_13_1164 : exactInterval 13 1164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1164 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1164) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1164 : oddCount 1164 13 = 6 ∧ acceleratedOrbit 13 1164 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1164 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1164) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1164.1, data_13_1164.2]

/-- Complete interval computation for depth 13, residue 1165. -/
theorem bounds_13_1165 : exactInterval 13 1165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1165 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1165) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1165 : oddCount 1165 13 = 6 ∧ acceleratedOrbit 13 1165 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1165 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1165) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1165.1, data_13_1165.2]

/-- Complete interval computation for depth 13, residue 1166. -/
theorem bounds_13_1166 : exactInterval 13 1166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1166 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1166) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1166 : oddCount 1166 13 = 6 ∧ acceleratedOrbit 13 1166 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1166 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1166) = 3 ^ 6 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1166.1, data_13_1166.2]

/-- Complete interval computation for depth 13, residue 1167. -/
theorem bounds_13_1167 : exactInterval 13 1167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1167 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1167) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1167 : oddCount 1167 13 = 6 ∧ acceleratedOrbit 13 1167 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1167 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1167) = 3 ^ 6 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1167.1, data_13_1167.2]

/-- Complete interval computation for depth 13, residue 1168. -/
theorem bounds_13_1168 : exactInterval 13 1168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1168 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1168) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1168 : oddCount 1168 13 = 6 ∧ acceleratedOrbit 13 1168 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1168 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1168) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1168.1, data_13_1168.2]

/-- Complete interval computation for depth 13, residue 1169. -/
theorem bounds_13_1169 : exactInterval 13 1169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1169 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1169) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1169 : oddCount 1169 13 = 7 ∧ acceleratedOrbit 13 1169 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1169 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1169) = 3 ^ 7 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1169.1, data_13_1169.2]

/-- Complete interval computation for depth 13, residue 1170. -/
theorem bounds_13_1170 : exactInterval 13 1170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1170 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1170) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1170 : oddCount 1170 13 = 7 ∧ acceleratedOrbit 13 1170 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1170 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1170) = 3 ^ 7 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1170.1, data_13_1170.2]

/-- Complete interval computation for depth 13, residue 1171. -/
theorem bounds_13_1171 : exactInterval 13 1171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1171 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1171) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1171 : oddCount 1171 13 = 7 ∧ acceleratedOrbit 13 1171 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1171 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1171) = 3 ^ 7 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1171.1, data_13_1171.2]

end Collatz.Research.StoppingAtlas.Batch0543
