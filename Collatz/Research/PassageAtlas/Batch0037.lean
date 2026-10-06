import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0037

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1179. -/
theorem bounds_15_1179 : exactInterval 15 1179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1179 : oddCount 1179 15 = 10 ∧ acceleratedOrbit 15 1179 = 2128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1179) = 3 ^ 10 * m + 2128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1179.1, data_15_1179.2]

/-- Complete interval computation for depth 15, residue 1180. -/
theorem bounds_15_1180 : exactInterval 15 1180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1180 : oddCount 1180 15 = 8 ∧ acceleratedOrbit 15 1180 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1180) = 3 ^ 8 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1180.1, data_15_1180.2]

/-- Complete interval computation for depth 15, residue 1181. -/
theorem bounds_15_1181 : exactInterval 15 1181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1181 : oddCount 1181 15 = 8 ∧ acceleratedOrbit 15 1181 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1181) = 3 ^ 8 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1181.1, data_15_1181.2]

/-- Complete interval computation for depth 15, residue 1182. -/
theorem bounds_15_1182 : exactInterval 15 1182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1182 : oddCount 1182 15 = 8 ∧ acceleratedOrbit 15 1182 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1182) = 3 ^ 8 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1182.1, data_15_1182.2]

/-- Complete interval computation for depth 15, residue 1183. -/
theorem bounds_15_1183 : exactInterval 15 1183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1183 : oddCount 1183 15 = 10 ∧ acceleratedOrbit 15 1183 = 2134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1183) = 3 ^ 10 * m + 2134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1183.1, data_15_1183.2]

/-- Complete interval computation for depth 15, residue 1184. -/
theorem bounds_15_1184 : exactInterval 15 1184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1184 : oddCount 1184 15 = 5 ∧ acceleratedOrbit 15 1184 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1184) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1184.1, data_15_1184.2]

/-- Complete interval computation for depth 15, residue 1185. -/
theorem bounds_15_1185 : exactInterval 15 1185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1185 : oddCount 1185 15 = 11 ∧ acceleratedOrbit 15 1185 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1185) = 3 ^ 11 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1185.1, data_15_1185.2]

/-- Complete interval computation for depth 15, residue 1186. -/
theorem bounds_15_1186 : exactInterval 15 1186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1186 : oddCount 1186 15 = 9 ∧ acceleratedOrbit 15 1186 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1186) = 3 ^ 9 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1186.1, data_15_1186.2]

/-- Complete interval computation for depth 15, residue 1187. -/
theorem bounds_15_1187 : exactInterval 15 1187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1187 : oddCount 1187 15 = 9 ∧ acceleratedOrbit 15 1187 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1187) = 3 ^ 9 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1187.1, data_15_1187.2]

/-- Complete interval computation for depth 15, residue 1188. -/
theorem bounds_15_1188 : exactInterval 15 1188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1188 : oddCount 1188 15 = 9 ∧ acceleratedOrbit 15 1188 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1188) = 3 ^ 9 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1188.1, data_15_1188.2]

/-- Complete interval computation for depth 15, residue 1189. -/
theorem bounds_15_1189 : exactInterval 15 1189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1189 : oddCount 1189 15 = 9 ∧ acceleratedOrbit 15 1189 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1189) = 3 ^ 9 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1189.1, data_15_1189.2]

/-- Complete interval computation for depth 15, residue 1190. -/
theorem bounds_15_1190 : exactInterval 15 1190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1190 : oddCount 1190 15 = 9 ∧ acceleratedOrbit 15 1190 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1190) = 3 ^ 9 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1190.1, data_15_1190.2]

/-- Complete interval computation for depth 15, residue 1191. -/
theorem bounds_15_1191 : exactInterval 15 1191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1191 : oddCount 1191 15 = 10 ∧ acceleratedOrbit 15 1191 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1191) = 3 ^ 10 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1191.1, data_15_1191.2]

/-- Complete interval computation for depth 15, residue 1192. -/
theorem bounds_15_1192 : exactInterval 15 1192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1192 : oddCount 1192 15 = 5 ∧ acceleratedOrbit 15 1192 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1192) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1192.1, data_15_1192.2]

/-- Complete interval computation for depth 15, residue 1193. -/
theorem bounds_15_1193 : exactInterval 15 1193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1193 : oddCount 1193 15 = 10 ∧ acceleratedOrbit 15 1193 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1193) = 3 ^ 10 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1193.1, data_15_1193.2]

/-- Complete interval computation for depth 15, residue 1194. -/
theorem bounds_15_1194 : exactInterval 15 1194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1194 : oddCount 1194 15 = 5 ∧ acceleratedOrbit 15 1194 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1194) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1194.1, data_15_1194.2]

/-- Complete interval computation for depth 15, residue 1195. -/
theorem bounds_15_1195 : exactInterval 15 1195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1195 : oddCount 1195 15 = 8 ∧ acceleratedOrbit 15 1195 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1195) = 3 ^ 8 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1195.1, data_15_1195.2]

/-- Complete interval computation for depth 15, residue 1196. -/
theorem bounds_15_1196 : exactInterval 15 1196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1196 : oddCount 1196 15 = 9 ∧ acceleratedOrbit 15 1196 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1196) = 3 ^ 9 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1196.1, data_15_1196.2]

/-- Complete interval computation for depth 15, residue 1197. -/
theorem bounds_15_1197 : exactInterval 15 1197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1197 : oddCount 1197 15 = 9 ∧ acceleratedOrbit 15 1197 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1197) = 3 ^ 9 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1197.1, data_15_1197.2]

/-- Complete interval computation for depth 15, residue 1198. -/
theorem bounds_15_1198 : exactInterval 15 1198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1198 : oddCount 1198 15 = 9 ∧ acceleratedOrbit 15 1198 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1198) = 3 ^ 9 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1198.1, data_15_1198.2]

/-- Complete interval computation for depth 15, residue 1199. -/
theorem bounds_15_1199 : exactInterval 15 1199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1199 : oddCount 1199 15 = 9 ∧ acceleratedOrbit 15 1199 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1199) = 3 ^ 9 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1199.1, data_15_1199.2]

/-- Complete interval computation for depth 15, residue 1200. -/
theorem bounds_15_1200 : exactInterval 15 1200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1200 : oddCount 1200 15 = 3 ∧ acceleratedOrbit 15 1200 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1200) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1200.1, data_15_1200.2]

/-- Complete interval computation for depth 15, residue 1201. -/
theorem bounds_15_1201 : exactInterval 15 1201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1201 : oddCount 1201 15 = 10 ∧ acceleratedOrbit 15 1201 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1201) = 3 ^ 10 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1201.1, data_15_1201.2]

/-- Complete interval computation for depth 15, residue 1202. -/
theorem bounds_15_1202 : exactInterval 15 1202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1202 : oddCount 1202 15 = 10 ∧ acceleratedOrbit 15 1202 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1202) = 3 ^ 10 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1202.1, data_15_1202.2]

/-- Complete interval computation for depth 15, residue 1203. -/
theorem bounds_15_1203 : exactInterval 15 1203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1203 : oddCount 1203 15 = 10 ∧ acceleratedOrbit 15 1203 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1203) = 3 ^ 10 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1203.1, data_15_1203.2]

/-- Complete interval computation for depth 15, residue 1204. -/
theorem bounds_15_1204 : exactInterval 15 1204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1204 : oddCount 1204 15 = 3 ∧ acceleratedOrbit 15 1204 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1204) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1204.1, data_15_1204.2]

/-- Complete interval computation for depth 15, residue 1205. -/
theorem bounds_15_1205 : exactInterval 15 1205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1205 : oddCount 1205 15 = 3 ∧ acceleratedOrbit 15 1205 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1205) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1205.1, data_15_1205.2]

/-- Complete interval computation for depth 15, residue 1206. -/
theorem bounds_15_1206 : exactInterval 15 1206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1206 : oddCount 1206 15 = 10 ∧ acceleratedOrbit 15 1206 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1206) = 3 ^ 10 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1206.1, data_15_1206.2]

/-- Complete interval computation for depth 15, residue 1207. -/
theorem bounds_15_1207 : exactInterval 15 1207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1207 : oddCount 1207 15 = 10 ∧ acceleratedOrbit 15 1207 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1207) = 3 ^ 10 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1207.1, data_15_1207.2]

/-- Complete interval computation for depth 15, residue 1208. -/
theorem bounds_15_1208 : exactInterval 15 1208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1208 : oddCount 1208 15 = 3 ∧ acceleratedOrbit 15 1208 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1208) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1208.1, data_15_1208.2]

/-- Complete interval computation for depth 15, residue 1209. -/
theorem bounds_15_1209 : exactInterval 15 1209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1209 : oddCount 1209 15 = 11 ∧ acceleratedOrbit 15 1209 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1209) = 3 ^ 11 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1209.1, data_15_1209.2]

/-- Complete interval computation for depth 15, residue 1210. -/
theorem bounds_15_1210 : exactInterval 15 1210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1210 : oddCount 1210 15 = 3 ∧ acceleratedOrbit 15 1210 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1210) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1210.1, data_15_1210.2]

/-- Complete interval computation for depth 15, residue 1211. -/
theorem bounds_15_1211 : exactInterval 15 1211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1211 : oddCount 1211 15 = 12 ∧ acceleratedOrbit 15 1211 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1211) = 3 ^ 12 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1211.1, data_15_1211.2]

end Collatz.Research.PassageAtlas.Batch0037
