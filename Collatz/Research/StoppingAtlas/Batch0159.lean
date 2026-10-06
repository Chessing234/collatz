import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0159

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1402. -/
theorem bounds_11_1402 : exactInterval 11 1402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1402 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1402) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1402 : oddCount 1402 11 = 5 ∧ acceleratedOrbit 11 1402 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1402 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1402) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1402.1, data_11_1402.2]

/-- Complete interval computation for depth 11, residue 1403. -/
theorem bounds_11_1403 : exactInterval 11 1403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1403 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1403) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1403 : oddCount 1403 11 = 6 ∧ acceleratedOrbit 11 1403 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1403 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1403) = 3 ^ 6 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1403.1, data_11_1403.2]

/-- Complete interval computation for depth 11, residue 1404. -/
theorem bounds_11_1404 : exactInterval 11 1404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1404 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1404) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1404 : oddCount 1404 11 = 5 ∧ acceleratedOrbit 11 1404 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1404 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1404) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1404.1, data_11_1404.2]

/-- Complete interval computation for depth 11, residue 1405. -/
theorem bounds_11_1405 : exactInterval 11 1405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1405 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1405) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1405 : oddCount 1405 11 = 5 ∧ acceleratedOrbit 11 1405 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1405 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1405) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1405.1, data_11_1405.2]

/-- Complete interval computation for depth 11, residue 1406. -/
theorem bounds_11_1406 : exactInterval 11 1406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1406 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1406) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1406 : oddCount 1406 11 = 8 ∧ acceleratedOrbit 11 1406 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1406 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1406) = 3 ^ 8 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1406.1, data_11_1406.2]

/-- Complete interval computation for depth 11, residue 1407. -/
theorem bounds_11_1407 : exactInterval 11 1407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1407 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1407) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1407 : oddCount 1407 11 = 8 ∧ acceleratedOrbit 11 1407 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1407 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1407) = 3 ^ 8 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1407.1, data_11_1407.2]

/-- Complete interval computation for depth 11, residue 1408. -/
theorem bounds_11_1408 : exactInterval 11 1408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1408 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1408) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1408 : oddCount 1408 11 = 3 ∧ acceleratedOrbit 11 1408 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1408 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1408) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1408.1, data_11_1408.2]

/-- Complete interval computation for depth 11, residue 1409. -/
theorem bounds_11_1409 : exactInterval 11 1409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1409 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1409) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1409 : oddCount 1409 11 = 6 ∧ acceleratedOrbit 11 1409 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1409 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1409) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1409.1, data_11_1409.2]

/-- Complete interval computation for depth 11, residue 1410. -/
theorem bounds_11_1410 : exactInterval 11 1410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1410 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1410) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1410 : oddCount 1410 11 = 4 ∧ acceleratedOrbit 11 1410 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1410 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1410) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1410.1, data_11_1410.2]

/-- Complete interval computation for depth 11, residue 1411. -/
theorem bounds_11_1411 : exactInterval 11 1411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1411 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1411) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1411 : oddCount 1411 11 = 4 ∧ acceleratedOrbit 11 1411 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1411 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1411) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1411.1, data_11_1411.2]

/-- Complete interval computation for depth 11, residue 1412. -/
theorem bounds_11_1412 : exactInterval 11 1412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1412 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1412) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1412 : oddCount 1412 11 = 6 ∧ acceleratedOrbit 11 1412 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1412 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1412) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1412.1, data_11_1412.2]

/-- Complete interval computation for depth 11, residue 1413. -/
theorem bounds_11_1413 : exactInterval 11 1413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1413 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1413) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1413 : oddCount 1413 11 = 6 ∧ acceleratedOrbit 11 1413 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1413 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1413) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1413.1, data_11_1413.2]

/-- Complete interval computation for depth 11, residue 1414. -/
theorem bounds_11_1414 : exactInterval 11 1414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1414 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1414) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1414 : oddCount 1414 11 = 6 ∧ acceleratedOrbit 11 1414 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1414 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1414) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1414.1, data_11_1414.2]

/-- Complete interval computation for depth 11, residue 1415. -/
theorem bounds_11_1415 : exactInterval 11 1415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1415 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1415) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1415 : oddCount 1415 11 = 4 ∧ acceleratedOrbit 11 1415 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1415 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1415) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1415.1, data_11_1415.2]

/-- Complete interval computation for depth 11, residue 1416. -/
theorem bounds_11_1416 : exactInterval 11 1416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1416 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1416) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1416 : oddCount 1416 11 = 3 ∧ acceleratedOrbit 11 1416 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1416 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1416) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1416.1, data_11_1416.2]

/-- Complete interval computation for depth 11, residue 1417. -/
theorem bounds_11_1417 : exactInterval 11 1417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1417 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1417) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1417 : oddCount 1417 11 = 6 ∧ acceleratedOrbit 11 1417 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1417 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1417) = 3 ^ 6 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1417.1, data_11_1417.2]

end Collatz.Research.StoppingAtlas.Batch0159
