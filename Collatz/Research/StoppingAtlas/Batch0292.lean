import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0292

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1397. -/
theorem bounds_12_1397 : exactInterval 12 1397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1397 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1397) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1397 : oddCount 1397 12 = 4 ∧ acceleratedOrbit 12 1397 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1397 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1397) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1397.1, data_12_1397.2]

/-- Complete interval computation for depth 12, residue 1398. -/
theorem bounds_12_1398 : exactInterval 12 1398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1398 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1398) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1398 : oddCount 1398 12 = 7 ∧ acceleratedOrbit 12 1398 = 749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1398 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1398) = 3 ^ 7 * m + 749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1398.1, data_12_1398.2]

/-- Complete interval computation for depth 12, residue 1399. -/
theorem bounds_12_1399 : exactInterval 12 1399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1399 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1399) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1399 : oddCount 1399 12 = 7 ∧ acceleratedOrbit 12 1399 = 749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1399 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1399) = 3 ^ 7 * m + 749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1399.1, data_12_1399.2]

/-- Complete interval computation for depth 12, residue 1400. -/
theorem bounds_12_1400 : exactInterval 12 1400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1400 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1400) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1400 : oddCount 1400 12 = 6 ∧ acceleratedOrbit 12 1400 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1400 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1400) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1400.1, data_12_1400.2]

/-- Complete interval computation for depth 12, residue 1401. -/
theorem bounds_12_1401 : exactInterval 12 1401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1401 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1401) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1401 : oddCount 1401 12 = 9 ∧ acceleratedOrbit 12 1401 = 6743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1401 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1401) = 3 ^ 9 * m + 6743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1401.1, data_12_1401.2]

/-- Complete interval computation for depth 12, residue 1402. -/
theorem bounds_12_1402 : exactInterval 12 1402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1402 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1402) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1402 : oddCount 1402 12 = 6 ∧ acceleratedOrbit 12 1402 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1402 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1402) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1402.1, data_12_1402.2]

/-- Complete interval computation for depth 12, residue 1403. -/
theorem bounds_12_1403 : exactInterval 12 1403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1403 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1403) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1403 : oddCount 1403 12 = 6 ∧ acceleratedOrbit 12 1403 = 250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1403 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1403) = 3 ^ 6 * m + 250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1403.1, data_12_1403.2]

/-- Complete interval computation for depth 12, residue 1404. -/
theorem bounds_12_1404 : exactInterval 12 1404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1404 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1404) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1404 : oddCount 1404 12 = 6 ∧ acceleratedOrbit 12 1404 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1404 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1404) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1404.1, data_12_1404.2]

/-- Complete interval computation for depth 12, residue 1405. -/
theorem bounds_12_1405 : exactInterval 12 1405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1405 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1405) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1405 : oddCount 1405 12 = 6 ∧ acceleratedOrbit 12 1405 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1405 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1405) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1405.1, data_12_1405.2]

/-- Complete interval computation for depth 12, residue 1406. -/
theorem bounds_12_1406 : exactInterval 12 1406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1406 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1406) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1406 : oddCount 1406 12 = 9 ∧ acceleratedOrbit 12 1406 = 6767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1406 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1406) = 3 ^ 9 * m + 6767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1406.1, data_12_1406.2]

/-- Complete interval computation for depth 12, residue 1407. -/
theorem bounds_12_1407 : exactInterval 12 1407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1407 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1407) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1407 : oddCount 1407 12 = 9 ∧ acceleratedOrbit 12 1407 = 6767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1407 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1407) = 3 ^ 9 * m + 6767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1407.1, data_12_1407.2]

/-- Complete interval computation for depth 12, residue 1408. -/
theorem bounds_12_1408 : exactInterval 12 1408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1408 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1408) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1408 : oddCount 1408 12 = 3 ∧ acceleratedOrbit 12 1408 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1408 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1408) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1408.1, data_12_1408.2]

/-- Complete interval computation for depth 12, residue 1409. -/
theorem bounds_12_1409 : exactInterval 12 1409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1409 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1409) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1409 : oddCount 1409 12 = 7 ∧ acceleratedOrbit 12 1409 = 755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1409 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1409) = 3 ^ 7 * m + 755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1409.1, data_12_1409.2]

/-- Complete interval computation for depth 12, residue 1410. -/
theorem bounds_12_1410 : exactInterval 12 1410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1410 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1410) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1410 : oddCount 1410 12 = 4 ∧ acceleratedOrbit 12 1410 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1410 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1410) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1410.1, data_12_1410.2]

/-- Complete interval computation for depth 12, residue 1411. -/
theorem bounds_12_1411 : exactInterval 12 1411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1411 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1411) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1411 : oddCount 1411 12 = 4 ∧ acceleratedOrbit 12 1411 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1411 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1411) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1411.1, data_12_1411.2]

/-- Complete interval computation for depth 12, residue 1412. -/
theorem bounds_12_1412 : exactInterval 12 1412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1412 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1412) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1412 : oddCount 1412 12 = 6 ∧ acceleratedOrbit 12 1412 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1412 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1412) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1412.1, data_12_1412.2]

end Collatz.Research.StoppingAtlas.Batch0292
