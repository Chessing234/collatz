import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0278

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1182. -/
theorem bounds_12_1182 : exactInterval 12 1182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1182 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1182) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1182 : oddCount 1182 12 = 6 ∧ acceleratedOrbit 12 1182 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1182 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1182) = 3 ^ 6 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1182.1, data_12_1182.2]

/-- Complete interval computation for depth 12, residue 1183. -/
theorem bounds_12_1183 : exactInterval 12 1183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1183 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1183) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1183 : oddCount 1183 12 = 9 ∧ acceleratedOrbit 12 1183 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1183 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1183) = 3 ^ 9 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1183.1, data_12_1183.2]

/-- Complete interval computation for depth 12, residue 1184. -/
theorem bounds_12_1184 : exactInterval 12 1184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1184 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1184) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1184 : oddCount 1184 12 = 4 ∧ acceleratedOrbit 12 1184 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1184 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1184) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1184.1, data_12_1184.2]

/-- Complete interval computation for depth 12, residue 1185. -/
theorem bounds_12_1185 : exactInterval 12 1185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1185 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1185) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1185 : oddCount 1185 12 = 8 ∧ acceleratedOrbit 12 1185 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1185 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1185) = 3 ^ 8 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1185.1, data_12_1185.2]

/-- Complete interval computation for depth 12, residue 1186. -/
theorem bounds_12_1186 : exactInterval 12 1186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1186 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1186) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1186 : oddCount 1186 12 = 7 ∧ acceleratedOrbit 12 1186 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1186 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1186) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1186.1, data_12_1186.2]

/-- Complete interval computation for depth 12, residue 1187. -/
theorem bounds_12_1187 : exactInterval 12 1187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1187 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1187) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1187 : oddCount 1187 12 = 7 ∧ acceleratedOrbit 12 1187 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1187 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1187) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1187.1, data_12_1187.2]

/-- Complete interval computation for depth 12, residue 1188. -/
theorem bounds_12_1188 : exactInterval 12 1188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1188 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1188) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1188 : oddCount 1188 12 = 7 ∧ acceleratedOrbit 12 1188 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1188 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1188) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1188.1, data_12_1188.2]

/-- Complete interval computation for depth 12, residue 1189. -/
theorem bounds_12_1189 : exactInterval 12 1189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1189 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1189) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1189 : oddCount 1189 12 = 7 ∧ acceleratedOrbit 12 1189 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1189 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1189) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1189.1, data_12_1189.2]

/-- Complete interval computation for depth 12, residue 1190. -/
theorem bounds_12_1190 : exactInterval 12 1190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1190 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1190) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1190 : oddCount 1190 12 = 7 ∧ acceleratedOrbit 12 1190 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1190 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1190) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1190.1, data_12_1190.2]

/-- Complete interval computation for depth 12, residue 1191. -/
theorem bounds_12_1191 : exactInterval 12 1191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1191 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1191) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1191 : oddCount 1191 12 = 8 ∧ acceleratedOrbit 12 1191 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1191 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1191) = 3 ^ 8 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1191.1, data_12_1191.2]

/-- Complete interval computation for depth 12, residue 1192. -/
theorem bounds_12_1192 : exactInterval 12 1192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1192 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1192) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1192 : oddCount 1192 12 = 4 ∧ acceleratedOrbit 12 1192 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1192 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1192) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1192.1, data_12_1192.2]

/-- Complete interval computation for depth 12, residue 1193. -/
theorem bounds_12_1193 : exactInterval 12 1193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1193 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1193) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1193 : oddCount 1193 12 = 9 ∧ acceleratedOrbit 12 1193 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1193 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1193) = 3 ^ 9 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1193.1, data_12_1193.2]

/-- Complete interval computation for depth 12, residue 1194. -/
theorem bounds_12_1194 : exactInterval 12 1194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1194 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1194) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1194 : oddCount 1194 12 = 4 ∧ acceleratedOrbit 12 1194 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1194 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1194) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1194.1, data_12_1194.2]

/-- Complete interval computation for depth 12, residue 1195. -/
theorem bounds_12_1195 : exactInterval 12 1195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1195 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1195) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1195 : oddCount 1195 12 = 5 ∧ acceleratedOrbit 12 1195 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1195 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1195) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1195.1, data_12_1195.2]

/-- Complete interval computation for depth 12, residue 1196. -/
theorem bounds_12_1196 : exactInterval 12 1196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1196 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1196) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1196 : oddCount 1196 12 = 6 ∧ acceleratedOrbit 12 1196 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1196 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1196) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1196.1, data_12_1196.2]

/-- Complete interval computation for depth 12, residue 1197. -/
theorem bounds_12_1197 : exactInterval 12 1197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1197 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1197) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1197 : oddCount 1197 12 = 6 ∧ acceleratedOrbit 12 1197 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1197 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1197) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1197.1, data_12_1197.2]

end Collatz.Research.StoppingAtlas.Batch0278
