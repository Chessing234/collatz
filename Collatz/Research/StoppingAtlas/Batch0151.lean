import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0151

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1280. -/
theorem bounds_11_1280 : exactInterval 11 1280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1280 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1280) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1280 : oddCount 1280 11 = 1 ∧ acceleratedOrbit 11 1280 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1280 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1280) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1280.1, data_11_1280.2]

/-- Complete interval computation for depth 11, residue 1281. -/
theorem bounds_11_1281 : exactInterval 11 1281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1281 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1281) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1281 : oddCount 1281 11 = 6 ∧ acceleratedOrbit 11 1281 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1281 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1281) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1281.1, data_11_1281.2]

/-- Complete interval computation for depth 11, residue 1282. -/
theorem bounds_11_1282 : exactInterval 11 1282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1282 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1282) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1282 : oddCount 1282 11 = 7 ∧ acceleratedOrbit 11 1282 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1282 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1282) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1282.1, data_11_1282.2]

/-- Complete interval computation for depth 11, residue 1283. -/
theorem bounds_11_1283 : exactInterval 11 1283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1283 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1283) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1283 : oddCount 1283 11 = 7 ∧ acceleratedOrbit 11 1283 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1283 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1283) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1283.1, data_11_1283.2]

/-- Complete interval computation for depth 11, residue 1284. -/
theorem bounds_11_1284 : exactInterval 11 1284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1284 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1284) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1284 : oddCount 1284 11 = 3 ∧ acceleratedOrbit 11 1284 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1284 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1284) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1284.1, data_11_1284.2]

/-- Complete interval computation for depth 11, residue 1285. -/
theorem bounds_11_1285 : exactInterval 11 1285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1285 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1285) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1285 : oddCount 1285 11 = 3 ∧ acceleratedOrbit 11 1285 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1285 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1285) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1285.1, data_11_1285.2]

/-- Complete interval computation for depth 11, residue 1286. -/
theorem bounds_11_1286 : exactInterval 11 1286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1286 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1286) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1286 : oddCount 1286 11 = 3 ∧ acceleratedOrbit 11 1286 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1286 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1286) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1286.1, data_11_1286.2]

/-- Complete interval computation for depth 11, residue 1287. -/
theorem bounds_11_1287 : exactInterval 11 1287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1287 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1287) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1287 : oddCount 1287 11 = 8 ∧ acceleratedOrbit 11 1287 = 4130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1287 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1287) = 3 ^ 8 * m + 4130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1287.1, data_11_1287.2]

/-- Complete interval computation for depth 11, residue 1288. -/
theorem bounds_11_1288 : exactInterval 11 1288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1288 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1288) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1288 : oddCount 1288 11 = 5 ∧ acceleratedOrbit 11 1288 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1288 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1288) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1288.1, data_11_1288.2]

/-- Complete interval computation for depth 11, residue 1289. -/
theorem bounds_11_1289 : exactInterval 11 1289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1289 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1289) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1289 : oddCount 1289 11 = 7 ∧ acceleratedOrbit 11 1289 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1289 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1289) = 3 ^ 7 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1289.1, data_11_1289.2]

/-- Complete interval computation for depth 11, residue 1290. -/
theorem bounds_11_1290 : exactInterval 11 1290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1290 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1290) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1290 : oddCount 1290 11 = 5 ∧ acceleratedOrbit 11 1290 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1290 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1290) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1290.1, data_11_1290.2]

/-- Complete interval computation for depth 11, residue 1291. -/
theorem bounds_11_1291 : exactInterval 11 1291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1291 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1291) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1291 : oddCount 1291 11 = 6 ∧ acceleratedOrbit 11 1291 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1291 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1291) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1291.1, data_11_1291.2]

/-- Complete interval computation for depth 11, residue 1292. -/
theorem bounds_11_1292 : exactInterval 11 1292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1292 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1292) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1292 : oddCount 1292 11 = 5 ∧ acceleratedOrbit 11 1292 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1292 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1292) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1292.1, data_11_1292.2]

/-- Complete interval computation for depth 11, residue 1293. -/
theorem bounds_11_1293 : exactInterval 11 1293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1293 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1293) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1293 : oddCount 1293 11 = 5 ∧ acceleratedOrbit 11 1293 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1293 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1293) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1293.1, data_11_1293.2]

/-- Complete interval computation for depth 11, residue 1294. -/
theorem bounds_11_1294 : exactInterval 11 1294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1294 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1294) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1294 : oddCount 1294 11 = 5 ∧ acceleratedOrbit 11 1294 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1294 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1294) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1294.1, data_11_1294.2]

end Collatz.Research.StoppingAtlas.Batch0151
