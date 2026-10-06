import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0558

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1387. -/
theorem bounds_13_1387 : exactInterval 13 1387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1387 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1387) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1387 : oddCount 1387 13 = 7 ∧ acceleratedOrbit 13 1387 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1387 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1387) = 3 ^ 7 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1387.1, data_13_1387.2]

/-- Complete interval computation for depth 13, residue 1388. -/
theorem bounds_13_1388 : exactInterval 13 1388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1388 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1388) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1388 : oddCount 1388 13 = 6 ∧ acceleratedOrbit 13 1388 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1388 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1388) = 3 ^ 6 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1388.1, data_13_1388.2]

/-- Complete interval computation for depth 13, residue 1389. -/
theorem bounds_13_1389 : exactInterval 13 1389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1389 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1389) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1389 : oddCount 1389 13 = 6 ∧ acceleratedOrbit 13 1389 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1389 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1389) = 3 ^ 6 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1389.1, data_13_1389.2]

/-- Complete interval computation for depth 13, residue 1390. -/
theorem bounds_13_1390 : exactInterval 13 1390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1390 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1390) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1390 : oddCount 1390 13 = 6 ∧ acceleratedOrbit 13 1390 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1390 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1390) = 3 ^ 6 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1390.1, data_13_1390.2]

/-- Complete interval computation for depth 13, residue 1391. -/
theorem bounds_13_1391 : exactInterval 13 1391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1391 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1391) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1391 : oddCount 1391 13 = 9 ∧ acceleratedOrbit 13 1391 = 3347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1391 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1391) = 3 ^ 9 * m + 3347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1391.1, data_13_1391.2]

/-- Complete interval computation for depth 13, residue 1392. -/
theorem bounds_13_1392 : exactInterval 13 1392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1392 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1392) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1392 : oddCount 1392 13 = 4 ∧ acceleratedOrbit 13 1392 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1392 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1392) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1392.1, data_13_1392.2]

/-- Complete interval computation for depth 13, residue 1393. -/
theorem bounds_13_1393 : exactInterval 13 1393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1393 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1393) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1393 : oddCount 1393 13 = 4 ∧ acceleratedOrbit 13 1393 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1393 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1393) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1393.1, data_13_1393.2]

/-- Complete interval computation for depth 13, residue 1394. -/
theorem bounds_13_1394 : exactInterval 13 1394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1394 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1394) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1394 : oddCount 1394 13 = 6 ∧ acceleratedOrbit 13 1394 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1394 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1394) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1394.1, data_13_1394.2]

/-- Complete interval computation for depth 13, residue 1395. -/
theorem bounds_13_1395 : exactInterval 13 1395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1395 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1395) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1395 : oddCount 1395 13 = 6 ∧ acceleratedOrbit 13 1395 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1395 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1395) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1395.1, data_13_1395.2]

/-- Complete interval computation for depth 13, residue 1396. -/
theorem bounds_13_1396 : exactInterval 13 1396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1396 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1396) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1396 : oddCount 1396 13 = 4 ∧ acceleratedOrbit 13 1396 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1396 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1396) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1396.1, data_13_1396.2]

/-- Complete interval computation for depth 13, residue 1397. -/
theorem bounds_13_1397 : exactInterval 13 1397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1397 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1397) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1397 : oddCount 1397 13 = 4 ∧ acceleratedOrbit 13 1397 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1397 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1397) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1397.1, data_13_1397.2]

/-- Complete interval computation for depth 13, residue 1398. -/
theorem bounds_13_1398 : exactInterval 13 1398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1398 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1398) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1398 : oddCount 1398 13 = 8 ∧ acceleratedOrbit 13 1398 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1398 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1398) = 3 ^ 8 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1398.1, data_13_1398.2]

/-- Complete interval computation for depth 13, residue 1399. -/
theorem bounds_13_1399 : exactInterval 13 1399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1399 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1399) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1399 : oddCount 1399 13 = 8 ∧ acceleratedOrbit 13 1399 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1399 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1399) = 3 ^ 8 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1399.1, data_13_1399.2]

/-- Complete interval computation for depth 13, residue 1400. -/
theorem bounds_13_1400 : exactInterval 13 1400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1400 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1400) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1400 : oddCount 1400 13 = 7 ∧ acceleratedOrbit 13 1400 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1400 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1400) = 3 ^ 7 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1400.1, data_13_1400.2]

/-- Complete interval computation for depth 13, residue 1401. -/
theorem bounds_13_1401 : exactInterval 13 1401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1401 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1401) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1401 : oddCount 1401 13 = 10 ∧ acceleratedOrbit 13 1401 = 10115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1401 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1401) = 3 ^ 10 * m + 10115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1401.1, data_13_1401.2]

end Collatz.Research.StoppingAtlas.Batch0558
