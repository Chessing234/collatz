import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0039

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1245. -/
theorem bounds_15_1245 : exactInterval 15 1245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1245 : oddCount 1245 15 = 8 ∧ acceleratedOrbit 15 1245 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1245) = 3 ^ 8 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1245.1, data_15_1245.2]

/-- Complete interval computation for depth 15, residue 1246. -/
theorem bounds_15_1246 : exactInterval 15 1246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1246 : oddCount 1246 15 = 8 ∧ acceleratedOrbit 15 1246 = 250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1246) = 3 ^ 8 * m + 250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1246.1, data_15_1246.2]

/-- Complete interval computation for depth 15, residue 1247. -/
theorem bounds_15_1247 : exactInterval 15 1247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1247 : oddCount 1247 15 = 8 ∧ acceleratedOrbit 15 1247 = 250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1247) = 3 ^ 8 * m + 250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1247.1, data_15_1247.2]

/-- Complete interval computation for depth 15, residue 1248. -/
theorem bounds_15_1248 : exactInterval 15 1248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1248 : oddCount 1248 15 = 6 ∧ acceleratedOrbit 15 1248 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1248) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1248.1, data_15_1248.2]

/-- Complete interval computation for depth 15, residue 1249. -/
theorem bounds_15_1249 : exactInterval 15 1249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1249 : oddCount 1249 15 = 11 ∧ acceleratedOrbit 15 1249 = 6767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1249) = 3 ^ 11 * m + 6767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1249.1, data_15_1249.2]

/-- Complete interval computation for depth 15, residue 1250. -/
theorem bounds_15_1250 : exactInterval 15 1250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1250 : oddCount 1250 15 = 5 ∧ acceleratedOrbit 15 1250 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1250) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1250.1, data_15_1250.2]

/-- Complete interval computation for depth 15, residue 1251. -/
theorem bounds_15_1251 : exactInterval 15 1251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1251 : oddCount 1251 15 = 5 ∧ acceleratedOrbit 15 1251 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1251) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1251.1, data_15_1251.2]

/-- Complete interval computation for depth 15, residue 1252. -/
theorem bounds_15_1252 : exactInterval 15 1252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1252 : oddCount 1252 15 = 8 ∧ acceleratedOrbit 15 1252 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1252) = 3 ^ 8 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1252.1, data_15_1252.2]

/-- Complete interval computation for depth 15, residue 1253. -/
theorem bounds_15_1253 : exactInterval 15 1253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1253 : oddCount 1253 15 = 8 ∧ acceleratedOrbit 15 1253 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1253) = 3 ^ 8 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1253.1, data_15_1253.2]

/-- Complete interval computation for depth 15, residue 1254. -/
theorem bounds_15_1254 : exactInterval 15 1254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1254 : oddCount 1254 15 = 8 ∧ acceleratedOrbit 15 1254 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1254) = 3 ^ 8 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1254.1, data_15_1254.2]

/-- Complete interval computation for depth 15, residue 1255. -/
theorem bounds_15_1255 : exactInterval 15 1255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1255 : oddCount 1255 15 = 11 ∧ acceleratedOrbit 15 1255 = 6794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1255) = 3 ^ 11 * m + 6794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1255.1, data_15_1255.2]

/-- Complete interval computation for depth 15, residue 1256. -/
theorem bounds_15_1256 : exactInterval 15 1256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1256 : oddCount 1256 15 = 6 ∧ acceleratedOrbit 15 1256 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1256) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1256.1, data_15_1256.2]

/-- Complete interval computation for depth 15, residue 1257. -/
theorem bounds_15_1257 : exactInterval 15 1257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1257 : oddCount 1257 15 = 6 ∧ acceleratedOrbit 15 1257 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1257) = 3 ^ 6 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1257.1, data_15_1257.2]

/-- Complete interval computation for depth 15, residue 1258. -/
theorem bounds_15_1258 : exactInterval 15 1258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1258 : oddCount 1258 15 = 6 ∧ acceleratedOrbit 15 1258 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1258) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1258.1, data_15_1258.2]

/-- Complete interval computation for depth 15, residue 1259. -/
theorem bounds_15_1259 : exactInterval 15 1259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1259 : oddCount 1259 15 = 9 ∧ acceleratedOrbit 15 1259 = 758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1259) = 3 ^ 9 * m + 758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1259.1, data_15_1259.2]

/-- Complete interval computation for depth 15, residue 1260. -/
theorem bounds_15_1260 : exactInterval 15 1260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1260 : oddCount 1260 15 = 6 ∧ acceleratedOrbit 15 1260 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1260) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1260.1, data_15_1260.2]

/-- Complete interval computation for depth 15, residue 1261. -/
theorem bounds_15_1261 : exactInterval 15 1261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1261 : oddCount 1261 15 = 6 ∧ acceleratedOrbit 15 1261 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1261) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1261.1, data_15_1261.2]

/-- Complete interval computation for depth 15, residue 1262. -/
theorem bounds_15_1262 : exactInterval 15 1262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1262 : oddCount 1262 15 = 6 ∧ acceleratedOrbit 15 1262 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1262) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1262.1, data_15_1262.2]

/-- Complete interval computation for depth 15, residue 1263. -/
theorem bounds_15_1263 : exactInterval 15 1263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1263 : oddCount 1263 15 = 12 ∧ acceleratedOrbit 15 1263 = 20503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1263) = 3 ^ 12 * m + 20503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1263.1, data_15_1263.2]

/-- Complete interval computation for depth 15, residue 1264. -/
theorem bounds_15_1264 : exactInterval 15 1264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1264 : oddCount 1264 15 = 6 ∧ acceleratedOrbit 15 1264 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1264) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1264.1, data_15_1264.2]

/-- Complete interval computation for depth 15, residue 1265. -/
theorem bounds_15_1265 : exactInterval 15 1265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1265 : oddCount 1265 15 = 6 ∧ acceleratedOrbit 15 1265 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1265) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1265.1, data_15_1265.2]

/-- Complete interval computation for depth 15, residue 1266. -/
theorem bounds_15_1266 : exactInterval 15 1266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1266 : oddCount 1266 15 = 7 ∧ acceleratedOrbit 15 1266 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1266) = 3 ^ 7 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1266.1, data_15_1266.2]

/-- Complete interval computation for depth 15, residue 1267. -/
theorem bounds_15_1267 : exactInterval 15 1267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1267 : oddCount 1267 15 = 7 ∧ acceleratedOrbit 15 1267 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1267) = 3 ^ 7 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1267.1, data_15_1267.2]

/-- Complete interval computation for depth 15, residue 1268. -/
theorem bounds_15_1268 : exactInterval 15 1268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1268 : oddCount 1268 15 = 6 ∧ acceleratedOrbit 15 1268 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1268) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1268.1, data_15_1268.2]

/-- Complete interval computation for depth 15, residue 1269. -/
theorem bounds_15_1269 : exactInterval 15 1269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1269 : oddCount 1269 15 = 6 ∧ acceleratedOrbit 15 1269 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1269) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1269.1, data_15_1269.2]

/-- Complete interval computation for depth 15, residue 1270. -/
theorem bounds_15_1270 : exactInterval 15 1270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1270 : oddCount 1270 15 = 8 ∧ acceleratedOrbit 15 1270 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1270) = 3 ^ 8 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1270.1, data_15_1270.2]

/-- Complete interval computation for depth 15, residue 1271. -/
theorem bounds_15_1271 : exactInterval 15 1271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1271 : oddCount 1271 15 = 8 ∧ acceleratedOrbit 15 1271 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1271) = 3 ^ 8 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1271.1, data_15_1271.2]

/-- Complete interval computation for depth 15, residue 1272. -/
theorem bounds_15_1272 : exactInterval 15 1272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1272 : oddCount 1272 15 = 10 ∧ acceleratedOrbit 15 1272 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1272) = 3 ^ 10 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1272.1, data_15_1272.2]

/-- Complete interval computation for depth 15, residue 1273. -/
theorem bounds_15_1273 : exactInterval 15 1273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1273 : oddCount 1273 15 = 8 ∧ acceleratedOrbit 15 1273 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1273) = 3 ^ 8 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1273.1, data_15_1273.2]

/-- Complete interval computation for depth 15, residue 1274. -/
theorem bounds_15_1274 : exactInterval 15 1274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1274 : oddCount 1274 15 = 10 ∧ acceleratedOrbit 15 1274 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1274) = 3 ^ 10 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1274.1, data_15_1274.2]

/-- Complete interval computation for depth 15, residue 1275. -/
theorem bounds_15_1275 : exactInterval 15 1275 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1275) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1275 : oddCount 1275 15 = 9 ∧ acceleratedOrbit 15 1275 = 767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1275) = 3 ^ 9 * m + 767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1275.1, data_15_1275.2]

/-- Complete interval computation for depth 15, residue 1276. -/
theorem bounds_15_1276 : exactInterval 15 1276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1276 : oddCount 1276 15 = 10 ∧ acceleratedOrbit 15 1276 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1276) = 3 ^ 10 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1276.1, data_15_1276.2]

end Collatz.Research.PassageAtlas.Batch0039
