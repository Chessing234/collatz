import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0559

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1402. -/
theorem bounds_13_1402 : exactInterval 13 1402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1402 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1402) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1402 : oddCount 1402 13 = 7 ∧ acceleratedOrbit 13 1402 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1402 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1402) = 3 ^ 7 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1402.1, data_13_1402.2]

/-- Complete interval computation for depth 13, residue 1403. -/
theorem bounds_13_1403 : exactInterval 13 1403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1403 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1403) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1403 : oddCount 1403 13 = 6 ∧ acceleratedOrbit 13 1403 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1403 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1403) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1403.1, data_13_1403.2]

/-- Complete interval computation for depth 13, residue 1404. -/
theorem bounds_13_1404 : exactInterval 13 1404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1404 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1404) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1404 : oddCount 1404 13 = 7 ∧ acceleratedOrbit 13 1404 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1404 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1404) = 3 ^ 7 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1404.1, data_13_1404.2]

/-- Complete interval computation for depth 13, residue 1405. -/
theorem bounds_13_1405 : exactInterval 13 1405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1405 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1405) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1405 : oddCount 1405 13 = 7 ∧ acceleratedOrbit 13 1405 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1405 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1405) = 3 ^ 7 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1405.1, data_13_1405.2]

/-- Complete interval computation for depth 13, residue 1406. -/
theorem bounds_13_1406 : exactInterval 13 1406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1406 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1406) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1406 : oddCount 1406 13 = 10 ∧ acceleratedOrbit 13 1406 = 10151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1406 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1406) = 3 ^ 10 * m + 10151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1406.1, data_13_1406.2]

/-- Complete interval computation for depth 13, residue 1407. -/
theorem bounds_13_1407 : exactInterval 13 1407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1407 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1407) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1407 : oddCount 1407 13 = 10 ∧ acceleratedOrbit 13 1407 = 10151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1407 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1407) = 3 ^ 10 * m + 10151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1407.1, data_13_1407.2]

/-- Complete interval computation for depth 13, residue 1408. -/
theorem bounds_13_1408 : exactInterval 13 1408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1408 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1408) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1408 : oddCount 1408 13 = 3 ∧ acceleratedOrbit 13 1408 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1408 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1408) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1408.1, data_13_1408.2]

/-- Complete interval computation for depth 13, residue 1409. -/
theorem bounds_13_1409 : exactInterval 13 1409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1409 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1409) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1409 : oddCount 1409 13 = 8 ∧ acceleratedOrbit 13 1409 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1409 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1409) = 3 ^ 8 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1409.1, data_13_1409.2]

/-- Complete interval computation for depth 13, residue 1410. -/
theorem bounds_13_1410 : exactInterval 13 1410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1410 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1410) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1410 : oddCount 1410 13 = 4 ∧ acceleratedOrbit 13 1410 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1410 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1410) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1410.1, data_13_1410.2]

/-- Complete interval computation for depth 13, residue 1411. -/
theorem bounds_13_1411 : exactInterval 13 1411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1411 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1411) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1411 : oddCount 1411 13 = 4 ∧ acceleratedOrbit 13 1411 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1411 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1411) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1411.1, data_13_1411.2]

/-- Complete interval computation for depth 13, residue 1412. -/
theorem bounds_13_1412 : exactInterval 13 1412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1412 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1412) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1412 : oddCount 1412 13 = 7 ∧ acceleratedOrbit 13 1412 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1412 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1412) = 3 ^ 7 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1412.1, data_13_1412.2]

/-- Complete interval computation for depth 13, residue 1413. -/
theorem bounds_13_1413 : exactInterval 13 1413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1413 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1413) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1413 : oddCount 1413 13 = 7 ∧ acceleratedOrbit 13 1413 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1413 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1413) = 3 ^ 7 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1413.1, data_13_1413.2]

/-- Complete interval computation for depth 13, residue 1414. -/
theorem bounds_13_1414 : exactInterval 13 1414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1414 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1414) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1414 : oddCount 1414 13 = 7 ∧ acceleratedOrbit 13 1414 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1414 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1414) = 3 ^ 7 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1414.1, data_13_1414.2]

/-- Complete interval computation for depth 13, residue 1415. -/
theorem bounds_13_1415 : exactInterval 13 1415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1415 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1415) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1415 : oddCount 1415 13 = 4 ∧ acceleratedOrbit 13 1415 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1415 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1415) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1415.1, data_13_1415.2]

/-- Complete interval computation for depth 13, residue 1416. -/
theorem bounds_13_1416 : exactInterval 13 1416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1416 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1416) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1416 : oddCount 1416 13 = 5 ∧ acceleratedOrbit 13 1416 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1416 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1416) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1416.1, data_13_1416.2]

/-- Complete interval computation for depth 13, residue 1417. -/
theorem bounds_13_1417 : exactInterval 13 1417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1417 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1417) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1417 : oddCount 1417 13 = 7 ∧ acceleratedOrbit 13 1417 = 379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1417 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1417) = 3 ^ 7 * m + 379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1417.1, data_13_1417.2]

end Collatz.Research.StoppingAtlas.Batch0559
