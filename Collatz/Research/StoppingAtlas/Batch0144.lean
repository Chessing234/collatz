import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0144

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1172. -/
theorem bounds_11_1172 : exactInterval 11 1172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1172 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1172) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1172 : oddCount 1172 11 = 4 ∧ acceleratedOrbit 11 1172 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1172 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1172) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1172.1, data_11_1172.2]

/-- Complete interval computation for depth 11, residue 1173. -/
theorem bounds_11_1173 : exactInterval 11 1173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1173 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1173) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1173 : oddCount 1173 11 = 4 ∧ acceleratedOrbit 11 1173 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1173 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1173) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1173.1, data_11_1173.2]

/-- Complete interval computation for depth 11, residue 1174. -/
theorem bounds_11_1174 : exactInterval 11 1174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1174 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1174) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1174 : oddCount 1174 11 = 4 ∧ acceleratedOrbit 11 1174 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1174 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1174) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1174.1, data_11_1174.2]

/-- Complete interval computation for depth 11, residue 1175. -/
theorem bounds_11_1175 : exactInterval 11 1175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1175 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1175) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1175 : oddCount 1175 11 = 4 ∧ acceleratedOrbit 11 1175 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1175 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1175) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1175.1, data_11_1175.2]

/-- Complete interval computation for depth 11, residue 1176. -/
theorem bounds_11_1176 : exactInterval 11 1176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1176 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1176) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1176 : oddCount 1176 11 = 4 ∧ acceleratedOrbit 11 1176 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1176 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1176) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1176.1, data_11_1176.2]

/-- Complete interval computation for depth 11, residue 1177. -/
theorem bounds_11_1177 : exactInterval 11 1177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1177 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1177) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1177 : oddCount 1177 11 = 5 ∧ acceleratedOrbit 11 1177 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1177 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1177) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1177.1, data_11_1177.2]

/-- Complete interval computation for depth 11, residue 1178. -/
theorem bounds_11_1178 : exactInterval 11 1178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1178 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1178) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1178 : oddCount 1178 11 = 4 ∧ acceleratedOrbit 11 1178 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1178 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1178) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1178.1, data_11_1178.2]

/-- Complete interval computation for depth 11, residue 1179. -/
theorem bounds_11_1179 : exactInterval 11 1179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1179 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1179) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1179 : oddCount 1179 11 = 8 ∧ acceleratedOrbit 11 1179 = 3782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1179 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1179) = 3 ^ 8 * m + 3782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1179.1, data_11_1179.2]

/-- Complete interval computation for depth 11, residue 1180. -/
theorem bounds_11_1180 : exactInterval 11 1180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1180 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1180) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1180 : oddCount 1180 11 = 6 ∧ acceleratedOrbit 11 1180 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1180 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1180) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1180.1, data_11_1180.2]

/-- Complete interval computation for depth 11, residue 1181. -/
theorem bounds_11_1181 : exactInterval 11 1181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1181 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1181) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1181 : oddCount 1181 11 = 6 ∧ acceleratedOrbit 11 1181 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1181 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1181) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1181.1, data_11_1181.2]

/-- Complete interval computation for depth 11, residue 1182. -/
theorem bounds_11_1182 : exactInterval 11 1182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1182 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1182) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1182 : oddCount 1182 11 = 6 ∧ acceleratedOrbit 11 1182 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1182 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1182) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1182.1, data_11_1182.2]

/-- Complete interval computation for depth 11, residue 1183. -/
theorem bounds_11_1183 : exactInterval 11 1183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1183 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1183) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1183 : oddCount 1183 11 = 9 ∧ acceleratedOrbit 11 1183 = 11380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1183 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1183) = 3 ^ 9 * m + 11380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1183.1, data_11_1183.2]

/-- Complete interval computation for depth 11, residue 1184. -/
theorem bounds_11_1184 : exactInterval 11 1184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1184 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1184) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1184 : oddCount 1184 11 = 3 ∧ acceleratedOrbit 11 1184 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1184 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1184) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1184.1, data_11_1184.2]

/-- Complete interval computation for depth 11, residue 1185. -/
theorem bounds_11_1185 : exactInterval 11 1185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1185 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1185) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1185 : oddCount 1185 11 = 8 ∧ acceleratedOrbit 11 1185 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1185 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1185) = 3 ^ 8 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1185.1, data_11_1185.2]

/-- Complete interval computation for depth 11, residue 1186. -/
theorem bounds_11_1186 : exactInterval 11 1186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1186 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1186) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1186 : oddCount 1186 11 = 6 ∧ acceleratedOrbit 11 1186 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1186 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1186) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1186.1, data_11_1186.2]

end Collatz.Research.StoppingAtlas.Batch0144
