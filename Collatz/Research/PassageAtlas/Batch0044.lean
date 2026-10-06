import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0044

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1409. -/
theorem bounds_15_1409 : exactInterval 15 1409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1409 : oddCount 1409 15 = 9 ∧ acceleratedOrbit 15 1409 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1409) = 3 ^ 9 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1409.1, data_15_1409.2]

/-- Complete interval computation for depth 15, residue 1410. -/
theorem bounds_15_1410 : exactInterval 15 1410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1410 : oddCount 1410 15 = 5 ∧ acceleratedOrbit 15 1410 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1410) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1410.1, data_15_1410.2]

/-- Complete interval computation for depth 15, residue 1411. -/
theorem bounds_15_1411 : exactInterval 15 1411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1411 : oddCount 1411 15 = 5 ∧ acceleratedOrbit 15 1411 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1411) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1411.1, data_15_1411.2]

/-- Complete interval computation for depth 15, residue 1412. -/
theorem bounds_15_1412 : exactInterval 15 1412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1412 : oddCount 1412 15 = 7 ∧ acceleratedOrbit 15 1412 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1412) = 3 ^ 7 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1412.1, data_15_1412.2]

/-- Complete interval computation for depth 15, residue 1413. -/
theorem bounds_15_1413 : exactInterval 15 1413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1413 : oddCount 1413 15 = 7 ∧ acceleratedOrbit 15 1413 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1413) = 3 ^ 7 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1413.1, data_15_1413.2]

/-- Complete interval computation for depth 15, residue 1414. -/
theorem bounds_15_1414 : exactInterval 15 1414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1414 : oddCount 1414 15 = 7 ∧ acceleratedOrbit 15 1414 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1414) = 3 ^ 7 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1414.1, data_15_1414.2]

/-- Complete interval computation for depth 15, residue 1415. -/
theorem bounds_15_1415 : exactInterval 15 1415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1415 : oddCount 1415 15 = 5 ∧ acceleratedOrbit 15 1415 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1415) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1415.1, data_15_1415.2]

/-- Complete interval computation for depth 15, residue 1416. -/
theorem bounds_15_1416 : exactInterval 15 1416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1416 : oddCount 1416 15 = 5 ∧ acceleratedOrbit 15 1416 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1416) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1416.1, data_15_1416.2]

/-- Complete interval computation for depth 15, residue 1417. -/
theorem bounds_15_1417 : exactInterval 15 1417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1417 : oddCount 1417 15 = 9 ∧ acceleratedOrbit 15 1417 = 854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1417) = 3 ^ 9 * m + 854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1417.1, data_15_1417.2]

/-- Complete interval computation for depth 15, residue 1418. -/
theorem bounds_15_1418 : exactInterval 15 1418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1418 : oddCount 1418 15 = 5 ∧ acceleratedOrbit 15 1418 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1418) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1418.1, data_15_1418.2]

/-- Complete interval computation for depth 15, residue 1419. -/
theorem bounds_15_1419 : exactInterval 15 1419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1419 : oddCount 1419 15 = 7 ∧ acceleratedOrbit 15 1419 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1419) = 3 ^ 7 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1419.1, data_15_1419.2]

/-- Complete interval computation for depth 15, residue 1420. -/
theorem bounds_15_1420 : exactInterval 15 1420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1420 : oddCount 1420 15 = 5 ∧ acceleratedOrbit 15 1420 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1420) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1420.1, data_15_1420.2]

/-- Complete interval computation for depth 15, residue 1421. -/
theorem bounds_15_1421 : exactInterval 15 1421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1421 : oddCount 1421 15 = 5 ∧ acceleratedOrbit 15 1421 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1421) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1421.1, data_15_1421.2]

/-- Complete interval computation for depth 15, residue 1422. -/
theorem bounds_15_1422 : exactInterval 15 1422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1422 : oddCount 1422 15 = 8 ∧ acceleratedOrbit 15 1422 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1422) = 3 ^ 8 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1422.1, data_15_1422.2]

/-- Complete interval computation for depth 15, residue 1423. -/
theorem bounds_15_1423 : exactInterval 15 1423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1423 : oddCount 1423 15 = 8 ∧ acceleratedOrbit 15 1423 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1423) = 3 ^ 8 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1423.1, data_15_1423.2]

/-- Complete interval computation for depth 15, residue 1424. -/
theorem bounds_15_1424 : exactInterval 15 1424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1424 : oddCount 1424 15 = 5 ∧ acceleratedOrbit 15 1424 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1424) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1424.1, data_15_1424.2]

/-- Complete interval computation for depth 15, residue 1425. -/
theorem bounds_15_1425 : exactInterval 15 1425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1425 : oddCount 1425 15 = 6 ∧ acceleratedOrbit 15 1425 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1425) = 3 ^ 6 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1425.1, data_15_1425.2]

/-- Complete interval computation for depth 15, residue 1426. -/
theorem bounds_15_1426 : exactInterval 15 1426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1426 : oddCount 1426 15 = 6 ∧ acceleratedOrbit 15 1426 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1426) = 3 ^ 6 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1426.1, data_15_1426.2]

/-- Complete interval computation for depth 15, residue 1427. -/
theorem bounds_15_1427 : exactInterval 15 1427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1427 : oddCount 1427 15 = 6 ∧ acceleratedOrbit 15 1427 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1427) = 3 ^ 6 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1427.1, data_15_1427.2]

/-- Complete interval computation for depth 15, residue 1428. -/
theorem bounds_15_1428 : exactInterval 15 1428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1428 : oddCount 1428 15 = 5 ∧ acceleratedOrbit 15 1428 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1428) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1428.1, data_15_1428.2]

/-- Complete interval computation for depth 15, residue 1429. -/
theorem bounds_15_1429 : exactInterval 15 1429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1429 : oddCount 1429 15 = 5 ∧ acceleratedOrbit 15 1429 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1429) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1429.1, data_15_1429.2]

/-- Complete interval computation for depth 15, residue 1430. -/
theorem bounds_15_1430 : exactInterval 15 1430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1430 : oddCount 1430 15 = 6 ∧ acceleratedOrbit 15 1430 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1430) = 3 ^ 6 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1430.1, data_15_1430.2]

/-- Complete interval computation for depth 15, residue 1431. -/
theorem bounds_15_1431 : exactInterval 15 1431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1431 : oddCount 1431 15 = 6 ∧ acceleratedOrbit 15 1431 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1431) = 3 ^ 6 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1431.1, data_15_1431.2]

/-- Complete interval computation for depth 15, residue 1432. -/
theorem bounds_15_1432 : exactInterval 15 1432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1432 : oddCount 1432 15 = 5 ∧ acceleratedOrbit 15 1432 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1432) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1432.1, data_15_1432.2]

/-- Complete interval computation for depth 15, residue 1433. -/
theorem bounds_15_1433 : exactInterval 15 1433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1433 : oddCount 1433 15 = 6 ∧ acceleratedOrbit 15 1433 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1433) = 3 ^ 6 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1433.1, data_15_1433.2]

/-- Complete interval computation for depth 15, residue 1434. -/
theorem bounds_15_1434 : exactInterval 15 1434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1434 : oddCount 1434 15 = 5 ∧ acceleratedOrbit 15 1434 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1434) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1434.1, data_15_1434.2]

/-- Complete interval computation for depth 15, residue 1435. -/
theorem bounds_15_1435 : exactInterval 15 1435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1435 : oddCount 1435 15 = 10 ∧ acceleratedOrbit 15 1435 = 2591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1435) = 3 ^ 10 * m + 2591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1435.1, data_15_1435.2]

/-- Complete interval computation for depth 15, residue 1436. -/
theorem bounds_15_1436 : exactInterval 15 1436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1436 : oddCount 1436 15 = 9 ∧ acceleratedOrbit 15 1436 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1436) = 3 ^ 9 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1436.1, data_15_1436.2]

/-- Complete interval computation for depth 15, residue 1437. -/
theorem bounds_15_1437 : exactInterval 15 1437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1437 : oddCount 1437 15 = 9 ∧ acceleratedOrbit 15 1437 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1437) = 3 ^ 9 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1437.1, data_15_1437.2]

/-- Complete interval computation for depth 15, residue 1438. -/
theorem bounds_15_1438 : exactInterval 15 1438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1438 : oddCount 1438 15 = 9 ∧ acceleratedOrbit 15 1438 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1438) = 3 ^ 9 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1438.1, data_15_1438.2]

/-- Complete interval computation for depth 15, residue 1439. -/
theorem bounds_15_1439 : exactInterval 15 1439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1439 : oddCount 1439 15 = 11 ∧ acceleratedOrbit 15 1439 = 7786 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1439) = 3 ^ 11 * m + 7786 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1439.1, data_15_1439.2]

/-- Complete interval computation for depth 15, residue 1440. -/
theorem bounds_15_1440 : exactInterval 15 1440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1440 : oddCount 1440 15 = 4 ∧ acceleratedOrbit 15 1440 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1440) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1440.1, data_15_1440.2]

end Collatz.Research.PassageAtlas.Batch0044
