import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0551

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1280. -/
theorem bounds_13_1280 : exactInterval 13 1280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1280 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1280) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1280 : oddCount 1280 13 = 2 ∧ acceleratedOrbit 13 1280 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1280 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1280) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1280.1, data_13_1280.2]

/-- Complete interval computation for depth 13, residue 1281. -/
theorem bounds_13_1281 : exactInterval 13 1281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1281 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1281) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1281 : oddCount 1281 13 = 7 ∧ acceleratedOrbit 13 1281 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1281 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1281) = 3 ^ 7 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1281.1, data_13_1281.2]

/-- Complete interval computation for depth 13, residue 1282. -/
theorem bounds_13_1282 : exactInterval 13 1282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1282 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1282) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1282 : oddCount 1282 13 = 7 ∧ acceleratedOrbit 13 1282 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1282 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1282) = 3 ^ 7 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1282.1, data_13_1282.2]

/-- Complete interval computation for depth 13, residue 1283. -/
theorem bounds_13_1283 : exactInterval 13 1283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1283 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1283) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1283 : oddCount 1283 13 = 7 ∧ acceleratedOrbit 13 1283 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1283 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1283) = 3 ^ 7 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1283.1, data_13_1283.2]

/-- Complete interval computation for depth 13, residue 1284. -/
theorem bounds_13_1284 : exactInterval 13 1284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1284 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1284) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1284 : oddCount 1284 13 = 4 ∧ acceleratedOrbit 13 1284 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1284 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1284) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1284.1, data_13_1284.2]

/-- Complete interval computation for depth 13, residue 1285. -/
theorem bounds_13_1285 : exactInterval 13 1285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1285 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1285) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1285 : oddCount 1285 13 = 4 ∧ acceleratedOrbit 13 1285 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1285 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1285) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1285.1, data_13_1285.2]

/-- Complete interval computation for depth 13, residue 1286. -/
theorem bounds_13_1286 : exactInterval 13 1286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1286 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1286) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1286 : oddCount 1286 13 = 4 ∧ acceleratedOrbit 13 1286 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1286 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1286) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1286.1, data_13_1286.2]

/-- Complete interval computation for depth 13, residue 1287. -/
theorem bounds_13_1287 : exactInterval 13 1287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1287 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1287) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1287 : oddCount 1287 13 = 9 ∧ acceleratedOrbit 13 1287 = 3098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1287 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1287) = 3 ^ 9 * m + 3098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1287.1, data_13_1287.2]

/-- Complete interval computation for depth 13, residue 1288. -/
theorem bounds_13_1288 : exactInterval 13 1288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1288 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1288) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1288 : oddCount 1288 13 = 7 ∧ acceleratedOrbit 13 1288 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1288 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1288) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1288.1, data_13_1288.2]

/-- Complete interval computation for depth 13, residue 1289. -/
theorem bounds_13_1289 : exactInterval 13 1289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1289 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1289) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1289 : oddCount 1289 13 = 9 ∧ acceleratedOrbit 13 1289 = 3104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1289 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1289) = 3 ^ 9 * m + 3104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1289.1, data_13_1289.2]

/-- Complete interval computation for depth 13, residue 1290. -/
theorem bounds_13_1290 : exactInterval 13 1290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1290 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1290) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1290 : oddCount 1290 13 = 7 ∧ acceleratedOrbit 13 1290 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1290 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1290) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1290.1, data_13_1290.2]

/-- Complete interval computation for depth 13, residue 1291. -/
theorem bounds_13_1291 : exactInterval 13 1291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1291 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1291) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1291 : oddCount 1291 13 = 7 ∧ acceleratedOrbit 13 1291 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1291 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1291) = 3 ^ 7 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1291.1, data_13_1291.2]

/-- Complete interval computation for depth 13, residue 1292. -/
theorem bounds_13_1292 : exactInterval 13 1292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1292 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1292) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1292 : oddCount 1292 13 = 7 ∧ acceleratedOrbit 13 1292 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1292 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1292) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1292.1, data_13_1292.2]

/-- Complete interval computation for depth 13, residue 1293. -/
theorem bounds_13_1293 : exactInterval 13 1293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1293 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1293) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1293 : oddCount 1293 13 = 7 ∧ acceleratedOrbit 13 1293 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1293 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1293) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1293.1, data_13_1293.2]

/-- Complete interval computation for depth 13, residue 1294. -/
theorem bounds_13_1294 : exactInterval 13 1294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1294 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1294) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1294 : oddCount 1294 13 = 6 ∧ acceleratedOrbit 13 1294 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1294 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1294) = 3 ^ 6 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1294.1, data_13_1294.2]

end Collatz.Research.StoppingAtlas.Batch0551
