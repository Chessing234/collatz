import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0040

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1277. -/
theorem bounds_15_1277 : exactInterval 15 1277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1277 : oddCount 1277 15 = 10 ∧ acceleratedOrbit 15 1277 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1277) = 3 ^ 10 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1277.1, data_15_1277.2]

/-- Complete interval computation for depth 15, residue 1278. -/
theorem bounds_15_1278 : exactInterval 15 1278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1278 : oddCount 1278 15 = 12 ∧ acceleratedOrbit 15 1278 = 20762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1278) = 3 ^ 12 * m + 20762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1278.1, data_15_1278.2]

/-- Complete interval computation for depth 15, residue 1279. -/
theorem bounds_15_1279 : exactInterval 15 1279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1279 : oddCount 1279 15 = 12 ∧ acceleratedOrbit 15 1279 = 20762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1279) = 3 ^ 12 * m + 20762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1279.1, data_15_1279.2]

/-- Complete interval computation for depth 15, residue 1280. -/
theorem bounds_15_1280 : exactInterval 15 1280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1280 : oddCount 1280 15 = 3 ∧ acceleratedOrbit 15 1280 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1280) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1280.1, data_15_1280.2]

/-- Complete interval computation for depth 15, residue 1281. -/
theorem bounds_15_1281 : exactInterval 15 1281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1281 : oddCount 1281 15 = 7 ∧ acceleratedOrbit 15 1281 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1281) = 3 ^ 7 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1281.1, data_15_1281.2]

/-- Complete interval computation for depth 15, residue 1282. -/
theorem bounds_15_1282 : exactInterval 15 1282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1282 : oddCount 1282 15 = 7 ∧ acceleratedOrbit 15 1282 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1282) = 3 ^ 7 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1282.1, data_15_1282.2]

/-- Complete interval computation for depth 15, residue 1283. -/
theorem bounds_15_1283 : exactInterval 15 1283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1283 : oddCount 1283 15 = 7 ∧ acceleratedOrbit 15 1283 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1283) = 3 ^ 7 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1283.1, data_15_1283.2]

/-- Complete interval computation for depth 15, residue 1284. -/
theorem bounds_15_1284 : exactInterval 15 1284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1284 : oddCount 1284 15 = 5 ∧ acceleratedOrbit 15 1284 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1284) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1284.1, data_15_1284.2]

/-- Complete interval computation for depth 15, residue 1285. -/
theorem bounds_15_1285 : exactInterval 15 1285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1285 : oddCount 1285 15 = 5 ∧ acceleratedOrbit 15 1285 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1285) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1285.1, data_15_1285.2]

/-- Complete interval computation for depth 15, residue 1286. -/
theorem bounds_15_1286 : exactInterval 15 1286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1286 : oddCount 1286 15 = 5 ∧ acceleratedOrbit 15 1286 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1286) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1286.1, data_15_1286.2]

/-- Complete interval computation for depth 15, residue 1287. -/
theorem bounds_15_1287 : exactInterval 15 1287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1287 : oddCount 1287 15 = 10 ∧ acceleratedOrbit 15 1287 = 2324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1287) = 3 ^ 10 * m + 2324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1287.1, data_15_1287.2]

/-- Complete interval computation for depth 15, residue 1288. -/
theorem bounds_15_1288 : exactInterval 15 1288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1288 : oddCount 1288 15 = 8 ∧ acceleratedOrbit 15 1288 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1288) = 3 ^ 8 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1288.1, data_15_1288.2]

/-- Complete interval computation for depth 15, residue 1289. -/
theorem bounds_15_1289 : exactInterval 15 1289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1289 : oddCount 1289 15 = 9 ∧ acceleratedOrbit 15 1289 = 776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1289) = 3 ^ 9 * m + 776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1289.1, data_15_1289.2]

/-- Complete interval computation for depth 15, residue 1290. -/
theorem bounds_15_1290 : exactInterval 15 1290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1290 : oddCount 1290 15 = 8 ∧ acceleratedOrbit 15 1290 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1290) = 3 ^ 8 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1290.1, data_15_1290.2]

/-- Complete interval computation for depth 15, residue 1291. -/
theorem bounds_15_1291 : exactInterval 15 1291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1291 : oddCount 1291 15 = 8 ∧ acceleratedOrbit 15 1291 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1291) = 3 ^ 8 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1291.1, data_15_1291.2]

/-- Complete interval computation for depth 15, residue 1292. -/
theorem bounds_15_1292 : exactInterval 15 1292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1292 : oddCount 1292 15 = 8 ∧ acceleratedOrbit 15 1292 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1292) = 3 ^ 8 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1292.1, data_15_1292.2]

/-- Complete interval computation for depth 15, residue 1293. -/
theorem bounds_15_1293 : exactInterval 15 1293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1293 : oddCount 1293 15 = 8 ∧ acceleratedOrbit 15 1293 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1293) = 3 ^ 8 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1293.1, data_15_1293.2]

/-- Complete interval computation for depth 15, residue 1294. -/
theorem bounds_15_1294 : exactInterval 15 1294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1294 : oddCount 1294 15 = 6 ∧ acceleratedOrbit 15 1294 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1294) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1294.1, data_15_1294.2]

/-- Complete interval computation for depth 15, residue 1295. -/
theorem bounds_15_1295 : exactInterval 15 1295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1295 : oddCount 1295 15 = 6 ∧ acceleratedOrbit 15 1295 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1295) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1295.1, data_15_1295.2]

/-- Complete interval computation for depth 15, residue 1296. -/
theorem bounds_15_1296 : exactInterval 15 1296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1296 : oddCount 1296 15 = 5 ∧ acceleratedOrbit 15 1296 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1296) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1296.1, data_15_1296.2]

/-- Complete interval computation for depth 15, residue 1297. -/
theorem bounds_15_1297 : exactInterval 15 1297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1297 : oddCount 1297 15 = 8 ∧ acceleratedOrbit 15 1297 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1297) = 3 ^ 8 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1297.1, data_15_1297.2]

/-- Complete interval computation for depth 15, residue 1298. -/
theorem bounds_15_1298 : exactInterval 15 1298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1298 : oddCount 1298 15 = 10 ∧ acceleratedOrbit 15 1298 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1298) = 3 ^ 10 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1298.1, data_15_1298.2]

/-- Complete interval computation for depth 15, residue 1299. -/
theorem bounds_15_1299 : exactInterval 15 1299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1299 : oddCount 1299 15 = 10 ∧ acceleratedOrbit 15 1299 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1299) = 3 ^ 10 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1299.1, data_15_1299.2]

/-- Complete interval computation for depth 15, residue 1300. -/
theorem bounds_15_1300 : exactInterval 15 1300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1300 : oddCount 1300 15 = 5 ∧ acceleratedOrbit 15 1300 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1300) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1300.1, data_15_1300.2]

/-- Complete interval computation for depth 15, residue 1301. -/
theorem bounds_15_1301 : exactInterval 15 1301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1301 : oddCount 1301 15 = 5 ∧ acceleratedOrbit 15 1301 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1301) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1301.1, data_15_1301.2]

/-- Complete interval computation for depth 15, residue 1302. -/
theorem bounds_15_1302 : exactInterval 15 1302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1302 : oddCount 1302 15 = 8 ∧ acceleratedOrbit 15 1302 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1302) = 3 ^ 8 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1302.1, data_15_1302.2]

/-- Complete interval computation for depth 15, residue 1303. -/
theorem bounds_15_1303 : exactInterval 15 1303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1303 : oddCount 1303 15 = 8 ∧ acceleratedOrbit 15 1303 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1303) = 3 ^ 8 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1303.1, data_15_1303.2]

/-- Complete interval computation for depth 15, residue 1304. -/
theorem bounds_15_1304 : exactInterval 15 1304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1304 : oddCount 1304 15 = 5 ∧ acceleratedOrbit 15 1304 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1304) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1304.1, data_15_1304.2]

/-- Complete interval computation for depth 15, residue 1305. -/
theorem bounds_15_1305 : exactInterval 15 1305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1305 : oddCount 1305 15 = 8 ∧ acceleratedOrbit 15 1305 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1305) = 3 ^ 8 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1305.1, data_15_1305.2]

/-- Complete interval computation for depth 15, residue 1306. -/
theorem bounds_15_1306 : exactInterval 15 1306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1306 : oddCount 1306 15 = 5 ∧ acceleratedOrbit 15 1306 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1306) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1306.1, data_15_1306.2]

/-- Complete interval computation for depth 15, residue 1307. -/
theorem bounds_15_1307 : exactInterval 15 1307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1307 : oddCount 1307 15 = 13 ∧ acceleratedOrbit 15 1307 = 63665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1307) = 3 ^ 13 * m + 63665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1307.1, data_15_1307.2]

/-- Complete interval computation for depth 15, residue 1308. -/
theorem bounds_15_1308 : exactInterval 15 1308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1308 : oddCount 1308 15 = 10 ∧ acceleratedOrbit 15 1308 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1308) = 3 ^ 10 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1308.1, data_15_1308.2]

/-- Complete interval computation for depth 15, residue 1309. -/
theorem bounds_15_1309 : exactInterval 15 1309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1309 : oddCount 1309 15 = 10 ∧ acceleratedOrbit 15 1309 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1309) = 3 ^ 10 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1309.1, data_15_1309.2]

end Collatz.Research.PassageAtlas.Batch0040
