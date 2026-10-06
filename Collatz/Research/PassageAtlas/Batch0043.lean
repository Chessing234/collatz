import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0043

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1376. -/
theorem bounds_15_1376 : exactInterval 15 1376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1376 : oddCount 1376 15 = 5 ∧ acceleratedOrbit 15 1376 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1376) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1376.1, data_15_1376.2]

/-- Complete interval computation for depth 15, residue 1377. -/
theorem bounds_15_1377 : exactInterval 15 1377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1377 : oddCount 1377 15 = 9 ∧ acceleratedOrbit 15 1377 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1377) = 3 ^ 9 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1377.1, data_15_1377.2]

/-- Complete interval computation for depth 15, residue 1378. -/
theorem bounds_15_1378 : exactInterval 15 1378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1378 : oddCount 1378 15 = 7 ∧ acceleratedOrbit 15 1378 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1378) = 3 ^ 7 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1378.1, data_15_1378.2]

/-- Complete interval computation for depth 15, residue 1379. -/
theorem bounds_15_1379 : exactInterval 15 1379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1379 : oddCount 1379 15 = 7 ∧ acceleratedOrbit 15 1379 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1379) = 3 ^ 7 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1379.1, data_15_1379.2]

/-- Complete interval computation for depth 15, residue 1380. -/
theorem bounds_15_1380 : exactInterval 15 1380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1380 : oddCount 1380 15 = 7 ∧ acceleratedOrbit 15 1380 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1380) = 3 ^ 7 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1380.1, data_15_1380.2]

/-- Complete interval computation for depth 15, residue 1381. -/
theorem bounds_15_1381 : exactInterval 15 1381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1381 : oddCount 1381 15 = 7 ∧ acceleratedOrbit 15 1381 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1381) = 3 ^ 7 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1381.1, data_15_1381.2]

/-- Complete interval computation for depth 15, residue 1382. -/
theorem bounds_15_1382 : exactInterval 15 1382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1382 : oddCount 1382 15 = 7 ∧ acceleratedOrbit 15 1382 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1382) = 3 ^ 7 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1382.1, data_15_1382.2]

/-- Complete interval computation for depth 15, residue 1383. -/
theorem bounds_15_1383 : exactInterval 15 1383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1383 : oddCount 1383 15 = 10 ∧ acceleratedOrbit 15 1383 = 2495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1383) = 3 ^ 10 * m + 2495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1383.1, data_15_1383.2]

/-- Complete interval computation for depth 15, residue 1384. -/
theorem bounds_15_1384 : exactInterval 15 1384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1384 : oddCount 1384 15 = 5 ∧ acceleratedOrbit 15 1384 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1384) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1384.1, data_15_1384.2]

/-- Complete interval computation for depth 15, residue 1385. -/
theorem bounds_15_1385 : exactInterval 15 1385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1385 : oddCount 1385 15 = 9 ∧ acceleratedOrbit 15 1385 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1385) = 3 ^ 9 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1385.1, data_15_1385.2]

/-- Complete interval computation for depth 15, residue 1386. -/
theorem bounds_15_1386 : exactInterval 15 1386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1386 : oddCount 1386 15 = 5 ∧ acceleratedOrbit 15 1386 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1386) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1386.1, data_15_1386.2]

/-- Complete interval computation for depth 15, residue 1387. -/
theorem bounds_15_1387 : exactInterval 15 1387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1387 : oddCount 1387 15 = 9 ∧ acceleratedOrbit 15 1387 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1387) = 3 ^ 9 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1387.1, data_15_1387.2]

/-- Complete interval computation for depth 15, residue 1388. -/
theorem bounds_15_1388 : exactInterval 15 1388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1388 : oddCount 1388 15 = 6 ∧ acceleratedOrbit 15 1388 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1388) = 3 ^ 6 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1388.1, data_15_1388.2]

/-- Complete interval computation for depth 15, residue 1389. -/
theorem bounds_15_1389 : exactInterval 15 1389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1389 : oddCount 1389 15 = 6 ∧ acceleratedOrbit 15 1389 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1389) = 3 ^ 6 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1389.1, data_15_1389.2]

/-- Complete interval computation for depth 15, residue 1390. -/
theorem bounds_15_1390 : exactInterval 15 1390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1390 : oddCount 1390 15 = 6 ∧ acceleratedOrbit 15 1390 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1390) = 3 ^ 6 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1390.1, data_15_1390.2]

/-- Complete interval computation for depth 15, residue 1391. -/
theorem bounds_15_1391 : exactInterval 15 1391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1391 : oddCount 1391 15 = 11 ∧ acceleratedOrbit 15 1391 = 7532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1391) = 3 ^ 11 * m + 7532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1391.1, data_15_1391.2]

/-- Complete interval computation for depth 15, residue 1392. -/
theorem bounds_15_1392 : exactInterval 15 1392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1392 : oddCount 1392 15 = 5 ∧ acceleratedOrbit 15 1392 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1392) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1392.1, data_15_1392.2]

/-- Complete interval computation for depth 15, residue 1393. -/
theorem bounds_15_1393 : exactInterval 15 1393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1393 : oddCount 1393 15 = 5 ∧ acceleratedOrbit 15 1393 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1393) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1393.1, data_15_1393.2]

/-- Complete interval computation for depth 15, residue 1394. -/
theorem bounds_15_1394 : exactInterval 15 1394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1394 : oddCount 1394 15 = 7 ∧ acceleratedOrbit 15 1394 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1394) = 3 ^ 7 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1394.1, data_15_1394.2]

/-- Complete interval computation for depth 15, residue 1395. -/
theorem bounds_15_1395 : exactInterval 15 1395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1395 : oddCount 1395 15 = 7 ∧ acceleratedOrbit 15 1395 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1395) = 3 ^ 7 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1395.1, data_15_1395.2]

/-- Complete interval computation for depth 15, residue 1396. -/
theorem bounds_15_1396 : exactInterval 15 1396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1396 : oddCount 1396 15 = 5 ∧ acceleratedOrbit 15 1396 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1396) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1396.1, data_15_1396.2]

/-- Complete interval computation for depth 15, residue 1397. -/
theorem bounds_15_1397 : exactInterval 15 1397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1397 : oddCount 1397 15 = 5 ∧ acceleratedOrbit 15 1397 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1397) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1397.1, data_15_1397.2]

/-- Complete interval computation for depth 15, residue 1398. -/
theorem bounds_15_1398 : exactInterval 15 1398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1398 : oddCount 1398 15 = 8 ∧ acceleratedOrbit 15 1398 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1398) = 3 ^ 8 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1398.1, data_15_1398.2]

/-- Complete interval computation for depth 15, residue 1399. -/
theorem bounds_15_1399 : exactInterval 15 1399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1399 : oddCount 1399 15 = 8 ∧ acceleratedOrbit 15 1399 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1399) = 3 ^ 8 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1399.1, data_15_1399.2]

/-- Complete interval computation for depth 15, residue 1400. -/
theorem bounds_15_1400 : exactInterval 15 1400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1400 : oddCount 1400 15 = 8 ∧ acceleratedOrbit 15 1400 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1400) = 3 ^ 8 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1400.1, data_15_1400.2]

/-- Complete interval computation for depth 15, residue 1401. -/
theorem bounds_15_1401 : exactInterval 15 1401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1401 : oddCount 1401 15 = 12 ∧ acceleratedOrbit 15 1401 = 22760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1401) = 3 ^ 12 * m + 22760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1401.1, data_15_1401.2]

/-- Complete interval computation for depth 15, residue 1402. -/
theorem bounds_15_1402 : exactInterval 15 1402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1402 : oddCount 1402 15 = 8 ∧ acceleratedOrbit 15 1402 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1402) = 3 ^ 8 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1402.1, data_15_1402.2]

/-- Complete interval computation for depth 15, residue 1403. -/
theorem bounds_15_1403 : exactInterval 15 1403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1403 : oddCount 1403 15 = 7 ∧ acceleratedOrbit 15 1403 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1403) = 3 ^ 7 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1403.1, data_15_1403.2]

/-- Complete interval computation for depth 15, residue 1404. -/
theorem bounds_15_1404 : exactInterval 15 1404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1404 : oddCount 1404 15 = 8 ∧ acceleratedOrbit 15 1404 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1404) = 3 ^ 8 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1404.1, data_15_1404.2]

/-- Complete interval computation for depth 15, residue 1405. -/
theorem bounds_15_1405 : exactInterval 15 1405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1405 : oddCount 1405 15 = 8 ∧ acceleratedOrbit 15 1405 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1405) = 3 ^ 8 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1405.1, data_15_1405.2]

/-- Complete interval computation for depth 15, residue 1406. -/
theorem bounds_15_1406 : exactInterval 15 1406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1406 : oddCount 1406 15 = 12 ∧ acceleratedOrbit 15 1406 = 22841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1406) = 3 ^ 12 * m + 22841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1406.1, data_15_1406.2]

/-- Complete interval computation for depth 15, residue 1407. -/
theorem bounds_15_1407 : exactInterval 15 1407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1407 : oddCount 1407 15 = 12 ∧ acceleratedOrbit 15 1407 = 22841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1407) = 3 ^ 12 * m + 22841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1407.1, data_15_1407.2]

/-- Complete interval computation for depth 15, residue 1408. -/
theorem bounds_15_1408 : exactInterval 15 1408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1408 : oddCount 1408 15 = 4 ∧ acceleratedOrbit 15 1408 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1408) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1408.1, data_15_1408.2]

end Collatz.Research.PassageAtlas.Batch0043
