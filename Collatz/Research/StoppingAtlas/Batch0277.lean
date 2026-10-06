import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0277

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1167. -/
theorem bounds_12_1167 : exactInterval 12 1167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1167 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1167) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1167 : oddCount 1167 12 = 6 ∧ acceleratedOrbit 12 1167 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1167 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1167) = 3 ^ 6 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1167.1, data_12_1167.2]

/-- Complete interval computation for depth 12, residue 1168. -/
theorem bounds_12_1168 : exactInterval 12 1168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1168 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1168) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1168 : oddCount 1168 12 = 5 ∧ acceleratedOrbit 12 1168 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1168 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1168) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1168.1, data_12_1168.2]

/-- Complete interval computation for depth 12, residue 1169. -/
theorem bounds_12_1169 : exactInterval 12 1169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1169 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1169) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1169 : oddCount 1169 12 = 6 ∧ acceleratedOrbit 12 1169 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1169 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1169) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1169.1, data_12_1169.2]

/-- Complete interval computation for depth 12, residue 1170. -/
theorem bounds_12_1170 : exactInterval 12 1170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1170 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1170) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1170 : oddCount 1170 12 = 6 ∧ acceleratedOrbit 12 1170 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1170 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1170) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1170.1, data_12_1170.2]

/-- Complete interval computation for depth 12, residue 1171. -/
theorem bounds_12_1171 : exactInterval 12 1171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1171 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1171) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1171 : oddCount 1171 12 = 6 ∧ acceleratedOrbit 12 1171 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1171 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1171) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1171.1, data_12_1171.2]

/-- Complete interval computation for depth 12, residue 1172. -/
theorem bounds_12_1172 : exactInterval 12 1172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1172 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1172) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1172 : oddCount 1172 12 = 5 ∧ acceleratedOrbit 12 1172 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1172 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1172) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1172.1, data_12_1172.2]

/-- Complete interval computation for depth 12, residue 1173. -/
theorem bounds_12_1173 : exactInterval 12 1173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1173 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1173) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1173 : oddCount 1173 12 = 5 ∧ acceleratedOrbit 12 1173 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1173 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1173) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1173.1, data_12_1173.2]

/-- Complete interval computation for depth 12, residue 1174. -/
theorem bounds_12_1174 : exactInterval 12 1174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1174 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1174) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1174 : oddCount 1174 12 = 5 ∧ acceleratedOrbit 12 1174 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1174 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1174) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1174.1, data_12_1174.2]

/-- Complete interval computation for depth 12, residue 1175. -/
theorem bounds_12_1175 : exactInterval 12 1175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1175 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1175) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1175 : oddCount 1175 12 = 5 ∧ acceleratedOrbit 12 1175 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1175 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1175) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1175.1, data_12_1175.2]

/-- Complete interval computation for depth 12, residue 1176. -/
theorem bounds_12_1176 : exactInterval 12 1176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1176 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1176) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1176 : oddCount 1176 12 = 5 ∧ acceleratedOrbit 12 1176 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1176 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1176) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1176.1, data_12_1176.2]

/-- Complete interval computation for depth 12, residue 1177. -/
theorem bounds_12_1177 : exactInterval 12 1177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1177 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1177) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1177 : oddCount 1177 12 = 5 ∧ acceleratedOrbit 12 1177 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1177 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1177) = 3 ^ 5 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1177.1, data_12_1177.2]

/-- Complete interval computation for depth 12, residue 1178. -/
theorem bounds_12_1178 : exactInterval 12 1178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1178 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1178) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1178 : oddCount 1178 12 = 5 ∧ acceleratedOrbit 12 1178 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1178 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1178) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1178.1, data_12_1178.2]

/-- Complete interval computation for depth 12, residue 1179. -/
theorem bounds_12_1179 : exactInterval 12 1179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1179 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1179) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1179 : oddCount 1179 12 = 8 ∧ acceleratedOrbit 12 1179 = 1891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1179 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1179) = 3 ^ 8 * m + 1891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1179.1, data_12_1179.2]

/-- Complete interval computation for depth 12, residue 1180. -/
theorem bounds_12_1180 : exactInterval 12 1180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1180 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1180) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1180 : oddCount 1180 12 = 6 ∧ acceleratedOrbit 12 1180 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1180 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1180) = 3 ^ 6 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1180.1, data_12_1180.2]

/-- Complete interval computation for depth 12, residue 1181. -/
theorem bounds_12_1181 : exactInterval 12 1181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1181 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1181) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1181 : oddCount 1181 12 = 6 ∧ acceleratedOrbit 12 1181 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1181 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1181) = 3 ^ 6 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1181.1, data_12_1181.2]

end Collatz.Research.StoppingAtlas.Batch0277
