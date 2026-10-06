import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0038

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1212. -/
theorem bounds_15_1212 : exactInterval 15 1212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1212 : oddCount 1212 15 = 8 ∧ acceleratedOrbit 15 1212 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1212) = 3 ^ 8 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1212.1, data_15_1212.2]

/-- Complete interval computation for depth 15, residue 1213. -/
theorem bounds_15_1213 : exactInterval 15 1213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1213 : oddCount 1213 15 = 8 ∧ acceleratedOrbit 15 1213 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1213) = 3 ^ 8 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1213.1, data_15_1213.2]

/-- Complete interval computation for depth 15, residue 1214. -/
theorem bounds_15_1214 : exactInterval 15 1214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1214 : oddCount 1214 15 = 8 ∧ acceleratedOrbit 15 1214 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1214) = 3 ^ 8 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1214.1, data_15_1214.2]

/-- Complete interval computation for depth 15, residue 1215. -/
theorem bounds_15_1215 : exactInterval 15 1215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1215 : oddCount 1215 15 = 9 ∧ acceleratedOrbit 15 1215 = 731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1215) = 3 ^ 9 * m + 731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1215.1, data_15_1215.2]

/-- Complete interval computation for depth 15, residue 1216. -/
theorem bounds_15_1216 : exactInterval 15 1216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1216 : oddCount 1216 15 = 5 ∧ acceleratedOrbit 15 1216 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1216) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1216.1, data_15_1216.2]

/-- Complete interval computation for depth 15, residue 1217. -/
theorem bounds_15_1217 : exactInterval 15 1217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1217 : oddCount 1217 15 = 7 ∧ acceleratedOrbit 15 1217 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1217) = 3 ^ 7 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1217.1, data_15_1217.2]

/-- Complete interval computation for depth 15, residue 1218. -/
theorem bounds_15_1218 : exactInterval 15 1218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1218 : oddCount 1218 15 = 7 ∧ acceleratedOrbit 15 1218 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1218) = 3 ^ 7 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1218.1, data_15_1218.2]

/-- Complete interval computation for depth 15, residue 1219. -/
theorem bounds_15_1219 : exactInterval 15 1219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1219 : oddCount 1219 15 = 7 ∧ acceleratedOrbit 15 1219 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1219) = 3 ^ 7 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1219.1, data_15_1219.2]

/-- Complete interval computation for depth 15, residue 1220. -/
theorem bounds_15_1220 : exactInterval 15 1220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1220 : oddCount 1220 15 = 6 ∧ acceleratedOrbit 15 1220 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1220) = 3 ^ 6 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1220.1, data_15_1220.2]

/-- Complete interval computation for depth 15, residue 1221. -/
theorem bounds_15_1221 : exactInterval 15 1221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1221 : oddCount 1221 15 = 6 ∧ acceleratedOrbit 15 1221 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1221) = 3 ^ 6 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1221.1, data_15_1221.2]

/-- Complete interval computation for depth 15, residue 1222. -/
theorem bounds_15_1222 : exactInterval 15 1222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1222 : oddCount 1222 15 = 6 ∧ acceleratedOrbit 15 1222 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1222) = 3 ^ 6 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1222.1, data_15_1222.2]

/-- Complete interval computation for depth 15, residue 1223. -/
theorem bounds_15_1223 : exactInterval 15 1223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1223 : oddCount 1223 15 = 7 ∧ acceleratedOrbit 15 1223 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1223) = 3 ^ 7 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1223.1, data_15_1223.2]

/-- Complete interval computation for depth 15, residue 1224. -/
theorem bounds_15_1224 : exactInterval 15 1224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1224 : oddCount 1224 15 = 6 ∧ acceleratedOrbit 15 1224 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1224) = 3 ^ 6 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1224.1, data_15_1224.2]

/-- Complete interval computation for depth 15, residue 1225. -/
theorem bounds_15_1225 : exactInterval 15 1225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1225 : oddCount 1225 15 = 7 ∧ acceleratedOrbit 15 1225 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1225) = 3 ^ 7 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1225.1, data_15_1225.2]

/-- Complete interval computation for depth 15, residue 1226. -/
theorem bounds_15_1226 : exactInterval 15 1226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1226 : oddCount 1226 15 = 6 ∧ acceleratedOrbit 15 1226 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1226) = 3 ^ 6 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1226.1, data_15_1226.2]

/-- Complete interval computation for depth 15, residue 1227. -/
theorem bounds_15_1227 : exactInterval 15 1227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1227 : oddCount 1227 15 = 7 ∧ acceleratedOrbit 15 1227 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1227) = 3 ^ 7 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1227.1, data_15_1227.2]

/-- Complete interval computation for depth 15, residue 1228. -/
theorem bounds_15_1228 : exactInterval 15 1228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1228 : oddCount 1228 15 = 6 ∧ acceleratedOrbit 15 1228 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1228) = 3 ^ 6 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1228.1, data_15_1228.2]

/-- Complete interval computation for depth 15, residue 1229. -/
theorem bounds_15_1229 : exactInterval 15 1229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1229 : oddCount 1229 15 = 6 ∧ acceleratedOrbit 15 1229 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1229) = 3 ^ 6 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1229.1, data_15_1229.2]

/-- Complete interval computation for depth 15, residue 1230. -/
theorem bounds_15_1230 : exactInterval 15 1230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1230 : oddCount 1230 15 = 8 ∧ acceleratedOrbit 15 1230 = 247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1230) = 3 ^ 8 * m + 247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1230.1, data_15_1230.2]

/-- Complete interval computation for depth 15, residue 1231. -/
theorem bounds_15_1231 : exactInterval 15 1231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1231 : oddCount 1231 15 = 8 ∧ acceleratedOrbit 15 1231 = 247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1231) = 3 ^ 8 * m + 247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1231.1, data_15_1231.2]

/-- Complete interval computation for depth 15, residue 1232. -/
theorem bounds_15_1232 : exactInterval 15 1232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1232 : oddCount 1232 15 = 5 ∧ acceleratedOrbit 15 1232 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1232) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1232.1, data_15_1232.2]

/-- Complete interval computation for depth 15, residue 1233. -/
theorem bounds_15_1233 : exactInterval 15 1233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1233 : oddCount 1233 15 = 8 ∧ acceleratedOrbit 15 1233 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1233) = 3 ^ 8 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1233.1, data_15_1233.2]

/-- Complete interval computation for depth 15, residue 1234. -/
theorem bounds_15_1234 : exactInterval 15 1234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1234 : oddCount 1234 15 = 8 ∧ acceleratedOrbit 15 1234 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1234) = 3 ^ 8 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1234.1, data_15_1234.2]

/-- Complete interval computation for depth 15, residue 1235. -/
theorem bounds_15_1235 : exactInterval 15 1235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1235 : oddCount 1235 15 = 8 ∧ acceleratedOrbit 15 1235 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1235) = 3 ^ 8 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1235.1, data_15_1235.2]

/-- Complete interval computation for depth 15, residue 1236. -/
theorem bounds_15_1236 : exactInterval 15 1236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1236 : oddCount 1236 15 = 5 ∧ acceleratedOrbit 15 1236 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1236) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1236.1, data_15_1236.2]

/-- Complete interval computation for depth 15, residue 1237. -/
theorem bounds_15_1237 : exactInterval 15 1237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1237 : oddCount 1237 15 = 5 ∧ acceleratedOrbit 15 1237 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1237) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1237.1, data_15_1237.2]

/-- Complete interval computation for depth 15, residue 1238. -/
theorem bounds_15_1238 : exactInterval 15 1238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1238 : oddCount 1238 15 = 7 ∧ acceleratedOrbit 15 1238 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1238) = 3 ^ 7 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1238.1, data_15_1238.2]

/-- Complete interval computation for depth 15, residue 1239. -/
theorem bounds_15_1239 : exactInterval 15 1239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1239 : oddCount 1239 15 = 7 ∧ acceleratedOrbit 15 1239 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1239) = 3 ^ 7 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1239.1, data_15_1239.2]

/-- Complete interval computation for depth 15, residue 1240. -/
theorem bounds_15_1240 : exactInterval 15 1240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1240 : oddCount 1240 15 = 8 ∧ acceleratedOrbit 15 1240 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1240) = 3 ^ 8 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1240.1, data_15_1240.2]

/-- Complete interval computation for depth 15, residue 1241. -/
theorem bounds_15_1241 : exactInterval 15 1241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1241 : oddCount 1241 15 = 6 ∧ acceleratedOrbit 15 1241 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1241) = 3 ^ 6 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1241.1, data_15_1241.2]

/-- Complete interval computation for depth 15, residue 1242. -/
theorem bounds_15_1242 : exactInterval 15 1242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1242 : oddCount 1242 15 = 8 ∧ acceleratedOrbit 15 1242 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1242) = 3 ^ 8 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1242.1, data_15_1242.2]

/-- Complete interval computation for depth 15, residue 1243. -/
theorem bounds_15_1243 : exactInterval 15 1243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1243 : oddCount 1243 15 = 9 ∧ acceleratedOrbit 15 1243 = 749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1243) = 3 ^ 9 * m + 749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1243.1, data_15_1243.2]

/-- Complete interval computation for depth 15, residue 1244. -/
theorem bounds_15_1244 : exactInterval 15 1244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1244 : oddCount 1244 15 = 8 ∧ acceleratedOrbit 15 1244 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1244) = 3 ^ 8 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1244.1, data_15_1244.2]

end Collatz.Research.PassageAtlas.Batch0038
