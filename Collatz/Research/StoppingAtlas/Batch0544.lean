import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0544

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1172. -/
theorem bounds_13_1172 : exactInterval 13 1172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1172 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1172) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1172 : oddCount 1172 13 = 6 ∧ acceleratedOrbit 13 1172 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1172 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1172) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1172.1, data_13_1172.2]

/-- Complete interval computation for depth 13, residue 1173. -/
theorem bounds_13_1173 : exactInterval 13 1173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1173 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1173) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1173 : oddCount 1173 13 = 6 ∧ acceleratedOrbit 13 1173 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1173 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1173) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1173.1, data_13_1173.2]

/-- Complete interval computation for depth 13, residue 1174. -/
theorem bounds_13_1174 : exactInterval 13 1174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1174 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1174) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1174 : oddCount 1174 13 = 6 ∧ acceleratedOrbit 13 1174 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1174 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1174) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1174.1, data_13_1174.2]

/-- Complete interval computation for depth 13, residue 1175. -/
theorem bounds_13_1175 : exactInterval 13 1175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1175 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1175) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1175 : oddCount 1175 13 = 6 ∧ acceleratedOrbit 13 1175 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1175 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1175) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1175.1, data_13_1175.2]

/-- Complete interval computation for depth 13, residue 1176. -/
theorem bounds_13_1176 : exactInterval 13 1176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1176 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1176) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1176 : oddCount 1176 13 = 6 ∧ acceleratedOrbit 13 1176 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1176 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1176) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1176.1, data_13_1176.2]

/-- Complete interval computation for depth 13, residue 1177. -/
theorem bounds_13_1177 : exactInterval 13 1177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1177 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1177) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1177 : oddCount 1177 13 = 5 ∧ acceleratedOrbit 13 1177 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1177 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1177) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1177.1, data_13_1177.2]

/-- Complete interval computation for depth 13, residue 1178. -/
theorem bounds_13_1178 : exactInterval 13 1178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1178 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1178) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1178 : oddCount 1178 13 = 6 ∧ acceleratedOrbit 13 1178 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1178 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1178) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1178.1, data_13_1178.2]

/-- Complete interval computation for depth 13, residue 1179. -/
theorem bounds_13_1179 : exactInterval 13 1179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1179 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1179) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1179 : oddCount 1179 13 = 9 ∧ acceleratedOrbit 13 1179 = 2837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1179 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1179) = 3 ^ 9 * m + 2837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1179.1, data_13_1179.2]

/-- Complete interval computation for depth 13, residue 1180. -/
theorem bounds_13_1180 : exactInterval 13 1180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1180 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1180) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1180 : oddCount 1180 13 = 7 ∧ acceleratedOrbit 13 1180 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1180 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1180) = 3 ^ 7 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1180.1, data_13_1180.2]

/-- Complete interval computation for depth 13, residue 1181. -/
theorem bounds_13_1181 : exactInterval 13 1181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1181 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1181) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1181 : oddCount 1181 13 = 7 ∧ acceleratedOrbit 13 1181 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1181 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1181) = 3 ^ 7 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1181.1, data_13_1181.2]

/-- Complete interval computation for depth 13, residue 1182. -/
theorem bounds_13_1182 : exactInterval 13 1182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1182 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1182) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1182 : oddCount 1182 13 = 7 ∧ acceleratedOrbit 13 1182 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1182 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1182) = 3 ^ 7 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1182.1, data_13_1182.2]

/-- Complete interval computation for depth 13, residue 1183. -/
theorem bounds_13_1183 : exactInterval 13 1183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1183 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1183) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1183 : oddCount 1183 13 = 9 ∧ acceleratedOrbit 13 1183 = 2845 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1183 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1183) = 3 ^ 9 * m + 2845 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1183.1, data_13_1183.2]

/-- Complete interval computation for depth 13, residue 1184. -/
theorem bounds_13_1184 : exactInterval 13 1184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1184 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1184) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1184 : oddCount 1184 13 = 4 ∧ acceleratedOrbit 13 1184 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1184 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1184) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1184.1, data_13_1184.2]

/-- Complete interval computation for depth 13, residue 1185. -/
theorem bounds_13_1185 : exactInterval 13 1185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1185 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1185) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1185 : oddCount 1185 13 = 9 ∧ acceleratedOrbit 13 1185 = 2855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1185 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1185) = 3 ^ 9 * m + 2855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1185.1, data_13_1185.2]

/-- Complete interval computation for depth 13, residue 1186. -/
theorem bounds_13_1186 : exactInterval 13 1186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1186 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1186) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1186 : oddCount 1186 13 = 7 ∧ acceleratedOrbit 13 1186 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1186 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1186) = 3 ^ 7 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1186.1, data_13_1186.2]

end Collatz.Research.StoppingAtlas.Batch0544
