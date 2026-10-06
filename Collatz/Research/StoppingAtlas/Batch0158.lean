import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0158

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1387. -/
theorem bounds_11_1387 : exactInterval 11 1387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1387 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1387) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1387 : oddCount 1387 11 = 7 ∧ acceleratedOrbit 11 1387 = 1484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1387 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1387) = 3 ^ 7 * m + 1484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1387.1, data_11_1387.2]

/-- Complete interval computation for depth 11, residue 1388. -/
theorem bounds_11_1388 : exactInterval 11 1388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1388 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1388) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1388 : oddCount 1388 11 = 6 ∧ acceleratedOrbit 11 1388 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1388 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1388) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1388.1, data_11_1388.2]

/-- Complete interval computation for depth 11, residue 1389. -/
theorem bounds_11_1389 : exactInterval 11 1389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1389 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1389) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1389 : oddCount 1389 11 = 6 ∧ acceleratedOrbit 11 1389 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1389 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1389) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1389.1, data_11_1389.2]

/-- Complete interval computation for depth 11, residue 1390. -/
theorem bounds_11_1390 : exactInterval 11 1390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1390 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1390) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1390 : oddCount 1390 11 = 6 ∧ acceleratedOrbit 11 1390 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1390 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1390) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1390.1, data_11_1390.2]

/-- Complete interval computation for depth 11, residue 1391. -/
theorem bounds_11_1391 : exactInterval 11 1391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1391 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1391) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1391 : oddCount 1391 11 = 7 ∧ acceleratedOrbit 11 1391 = 1487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1391 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1391) = 3 ^ 7 * m + 1487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1391.1, data_11_1391.2]

/-- Complete interval computation for depth 11, residue 1392. -/
theorem bounds_11_1392 : exactInterval 11 1392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1392 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1392) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1392 : oddCount 1392 11 = 4 ∧ acceleratedOrbit 11 1392 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1392 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1392) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1392.1, data_11_1392.2]

/-- Complete interval computation for depth 11, residue 1393. -/
theorem bounds_11_1393 : exactInterval 11 1393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1393 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1393) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1393 : oddCount 1393 11 = 4 ∧ acceleratedOrbit 11 1393 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1393 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1393) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1393.1, data_11_1393.2]

/-- Complete interval computation for depth 11, residue 1394. -/
theorem bounds_11_1394 : exactInterval 11 1394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1394 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1394) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1394 : oddCount 1394 11 = 5 ∧ acceleratedOrbit 11 1394 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1394 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1394) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1394.1, data_11_1394.2]

/-- Complete interval computation for depth 11, residue 1395. -/
theorem bounds_11_1395 : exactInterval 11 1395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1395 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1395) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1395 : oddCount 1395 11 = 5 ∧ acceleratedOrbit 11 1395 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1395 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1395) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1395.1, data_11_1395.2]

/-- Complete interval computation for depth 11, residue 1396. -/
theorem bounds_11_1396 : exactInterval 11 1396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1396 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1396) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1396 : oddCount 1396 11 = 4 ∧ acceleratedOrbit 11 1396 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1396 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1396) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1396.1, data_11_1396.2]

/-- Complete interval computation for depth 11, residue 1397. -/
theorem bounds_11_1397 : exactInterval 11 1397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1397 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1397) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1397 : oddCount 1397 11 = 4 ∧ acceleratedOrbit 11 1397 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1397 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1397) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1397.1, data_11_1397.2]

/-- Complete interval computation for depth 11, residue 1398. -/
theorem bounds_11_1398 : exactInterval 11 1398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1398 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1398) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1398 : oddCount 1398 11 = 6 ∧ acceleratedOrbit 11 1398 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1398 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1398) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1398.1, data_11_1398.2]

/-- Complete interval computation for depth 11, residue 1399. -/
theorem bounds_11_1399 : exactInterval 11 1399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1399 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1399) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1399 : oddCount 1399 11 = 6 ∧ acceleratedOrbit 11 1399 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1399 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1399) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1399.1, data_11_1399.2]

/-- Complete interval computation for depth 11, residue 1400. -/
theorem bounds_11_1400 : exactInterval 11 1400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1400 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1400) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1400 : oddCount 1400 11 = 5 ∧ acceleratedOrbit 11 1400 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1400 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1400) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1400.1, data_11_1400.2]

/-- Complete interval computation for depth 11, residue 1401. -/
theorem bounds_11_1401 : exactInterval 11 1401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1401 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1401) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1401 : oddCount 1401 11 = 8 ∧ acceleratedOrbit 11 1401 = 4495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1401 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1401) = 3 ^ 8 * m + 4495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1401.1, data_11_1401.2]

end Collatz.Research.StoppingAtlas.Batch0158
