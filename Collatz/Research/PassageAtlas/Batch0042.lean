import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0042

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1343. -/
theorem bounds_15_1343 : exactInterval 15 1343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1343 : oddCount 1343 15 = 10 ∧ acceleratedOrbit 15 1343 = 2423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1343) = 3 ^ 10 * m + 2423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1343.1, data_15_1343.2]

/-- Complete interval computation for depth 15, residue 1344. -/
theorem bounds_15_1344 : exactInterval 15 1344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1344 : oddCount 1344 15 = 3 ∧ acceleratedOrbit 15 1344 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1344) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1344.1, data_15_1344.2]

/-- Complete interval computation for depth 15, residue 1345. -/
theorem bounds_15_1345 : exactInterval 15 1345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1345 : oddCount 1345 15 = 7 ∧ acceleratedOrbit 15 1345 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1345) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1345.1, data_15_1345.2]

/-- Complete interval computation for depth 15, residue 1346. -/
theorem bounds_15_1346 : exactInterval 15 1346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1346 : oddCount 1346 15 = 8 ∧ acceleratedOrbit 15 1346 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1346) = 3 ^ 8 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1346.1, data_15_1346.2]

/-- Complete interval computation for depth 15, residue 1347. -/
theorem bounds_15_1347 : exactInterval 15 1347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1347 : oddCount 1347 15 = 8 ∧ acceleratedOrbit 15 1347 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1347) = 3 ^ 8 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1347.1, data_15_1347.2]

/-- Complete interval computation for depth 15, residue 1348. -/
theorem bounds_15_1348 : exactInterval 15 1348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1348 : oddCount 1348 15 = 7 ∧ acceleratedOrbit 15 1348 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1348) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1348.1, data_15_1348.2]

/-- Complete interval computation for depth 15, residue 1349. -/
theorem bounds_15_1349 : exactInterval 15 1349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1349 : oddCount 1349 15 = 7 ∧ acceleratedOrbit 15 1349 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1349) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1349.1, data_15_1349.2]

/-- Complete interval computation for depth 15, residue 1350. -/
theorem bounds_15_1350 : exactInterval 15 1350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1350 : oddCount 1350 15 = 7 ∧ acceleratedOrbit 15 1350 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1350) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1350.1, data_15_1350.2]

/-- Complete interval computation for depth 15, residue 1351. -/
theorem bounds_15_1351 : exactInterval 15 1351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1351 : oddCount 1351 15 = 10 ∧ acceleratedOrbit 15 1351 = 2438 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1351) = 3 ^ 10 * m + 2438 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1351.1, data_15_1351.2]

/-- Complete interval computation for depth 15, residue 1352. -/
theorem bounds_15_1352 : exactInterval 15 1352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1352 : oddCount 1352 15 = 9 ∧ acceleratedOrbit 15 1352 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1352) = 3 ^ 9 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1352.1, data_15_1352.2]

/-- Complete interval computation for depth 15, residue 1353. -/
theorem bounds_15_1353 : exactInterval 15 1353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1353 : oddCount 1353 15 = 8 ∧ acceleratedOrbit 15 1353 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1353) = 3 ^ 8 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1353.1, data_15_1353.2]

/-- Complete interval computation for depth 15, residue 1354. -/
theorem bounds_15_1354 : exactInterval 15 1354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1354 : oddCount 1354 15 = 9 ∧ acceleratedOrbit 15 1354 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1354) = 3 ^ 9 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1354.1, data_15_1354.2]

/-- Complete interval computation for depth 15, residue 1355. -/
theorem bounds_15_1355 : exactInterval 15 1355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1355 : oddCount 1355 15 = 7 ∧ acceleratedOrbit 15 1355 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1355) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1355.1, data_15_1355.2]

/-- Complete interval computation for depth 15, residue 1356. -/
theorem bounds_15_1356 : exactInterval 15 1356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1356 : oddCount 1356 15 = 9 ∧ acceleratedOrbit 15 1356 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1356) = 3 ^ 9 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1356.1, data_15_1356.2]

/-- Complete interval computation for depth 15, residue 1357. -/
theorem bounds_15_1357 : exactInterval 15 1357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1357 : oddCount 1357 15 = 9 ∧ acceleratedOrbit 15 1357 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1357) = 3 ^ 9 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1357.1, data_15_1357.2]

/-- Complete interval computation for depth 15, residue 1358. -/
theorem bounds_15_1358 : exactInterval 15 1358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1358 : oddCount 1358 15 = 9 ∧ acceleratedOrbit 15 1358 = 818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1358) = 3 ^ 9 * m + 818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1358.1, data_15_1358.2]

/-- Complete interval computation for depth 15, residue 1359. -/
theorem bounds_15_1359 : exactInterval 15 1359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1359 : oddCount 1359 15 = 9 ∧ acceleratedOrbit 15 1359 = 818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1359) = 3 ^ 9 * m + 818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1359.1, data_15_1359.2]

/-- Complete interval computation for depth 15, residue 1360. -/
theorem bounds_15_1360 : exactInterval 15 1360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1360 : oddCount 1360 15 = 3 ∧ acceleratedOrbit 15 1360 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1360) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1360.1, data_15_1360.2]

/-- Complete interval computation for depth 15, residue 1361. -/
theorem bounds_15_1361 : exactInterval 15 1361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1361 : oddCount 1361 15 = 9 ∧ acceleratedOrbit 15 1361 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1361) = 3 ^ 9 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1361.1, data_15_1361.2]

/-- Complete interval computation for depth 15, residue 1362. -/
theorem bounds_15_1362 : exactInterval 15 1362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1362 : oddCount 1362 15 = 11 ∧ acceleratedOrbit 15 1362 = 7381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1362) = 3 ^ 11 * m + 7381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1362.1, data_15_1362.2]

/-- Complete interval computation for depth 15, residue 1363. -/
theorem bounds_15_1363 : exactInterval 15 1363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1363 : oddCount 1363 15 = 11 ∧ acceleratedOrbit 15 1363 = 7381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1363) = 3 ^ 11 * m + 7381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1363.1, data_15_1363.2]

/-- Complete interval computation for depth 15, residue 1364. -/
theorem bounds_15_1364 : exactInterval 15 1364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1364 : oddCount 1364 15 = 3 ∧ acceleratedOrbit 15 1364 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1364) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1364.1, data_15_1364.2]

/-- Complete interval computation for depth 15, residue 1365. -/
theorem bounds_15_1365 : exactInterval 15 1365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1365 : oddCount 1365 15 = 3 ∧ acceleratedOrbit 15 1365 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1365) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1365.1, data_15_1365.2]

/-- Complete interval computation for depth 15, residue 1366. -/
theorem bounds_15_1366 : exactInterval 15 1366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1366 : oddCount 1366 15 = 7 ∧ acceleratedOrbit 15 1366 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1366) = 3 ^ 7 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1366.1, data_15_1366.2]

/-- Complete interval computation for depth 15, residue 1367. -/
theorem bounds_15_1367 : exactInterval 15 1367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1367 : oddCount 1367 15 = 7 ∧ acceleratedOrbit 15 1367 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1367) = 3 ^ 7 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1367.1, data_15_1367.2]

/-- Complete interval computation for depth 15, residue 1368. -/
theorem bounds_15_1368 : exactInterval 15 1368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1368 : oddCount 1368 15 = 6 ∧ acceleratedOrbit 15 1368 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1368) = 3 ^ 6 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1368.1, data_15_1368.2]

/-- Complete interval computation for depth 15, residue 1369. -/
theorem bounds_15_1369 : exactInterval 15 1369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1369 : oddCount 1369 15 = 7 ∧ acceleratedOrbit 15 1369 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1369) = 3 ^ 7 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1369.1, data_15_1369.2]

/-- Complete interval computation for depth 15, residue 1370. -/
theorem bounds_15_1370 : exactInterval 15 1370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1370 : oddCount 1370 15 = 6 ∧ acceleratedOrbit 15 1370 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1370) = 3 ^ 6 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1370.1, data_15_1370.2]

/-- Complete interval computation for depth 15, residue 1371. -/
theorem bounds_15_1371 : exactInterval 15 1371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1371 : oddCount 1371 15 = 8 ∧ acceleratedOrbit 15 1371 = 275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1371) = 3 ^ 8 * m + 275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1371.1, data_15_1371.2]

/-- Complete interval computation for depth 15, residue 1372. -/
theorem bounds_15_1372 : exactInterval 15 1372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1372 : oddCount 1372 15 = 6 ∧ acceleratedOrbit 15 1372 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1372) = 3 ^ 6 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1372.1, data_15_1372.2]

/-- Complete interval computation for depth 15, residue 1373. -/
theorem bounds_15_1373 : exactInterval 15 1373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1373 : oddCount 1373 15 = 6 ∧ acceleratedOrbit 15 1373 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1373) = 3 ^ 6 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1373.1, data_15_1373.2]

/-- Complete interval computation for depth 15, residue 1374. -/
theorem bounds_15_1374 : exactInterval 15 1374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1374 : oddCount 1374 15 = 7 ∧ acceleratedOrbit 15 1374 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1374) = 3 ^ 7 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1374.1, data_15_1374.2]

/-- Complete interval computation for depth 15, residue 1375. -/
theorem bounds_15_1375 : exactInterval 15 1375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1375 : oddCount 1375 15 = 7 ∧ acceleratedOrbit 15 1375 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1375) = 3 ^ 7 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1375.1, data_15_1375.2]

end Collatz.Research.PassageAtlas.Batch0042
