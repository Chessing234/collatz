import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0291

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1382. -/
theorem bounds_12_1382 : exactInterval 12 1382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1382 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1382) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1382 : oddCount 1382 12 = 5 ∧ acceleratedOrbit 12 1382 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1382 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1382) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1382.1, data_12_1382.2]

/-- Complete interval computation for depth 12, residue 1383. -/
theorem bounds_12_1383 : exactInterval 12 1383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1383 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1383) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1383 : oddCount 1383 12 = 9 ∧ acceleratedOrbit 12 1383 = 6652 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1383 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1383) = 3 ^ 9 * m + 6652 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1383.1, data_12_1383.2]

/-- Complete interval computation for depth 12, residue 1384. -/
theorem bounds_12_1384 : exactInterval 12 1384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1384 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1384) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1384 : oddCount 1384 12 = 4 ∧ acceleratedOrbit 12 1384 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1384 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1384) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1384.1, data_12_1384.2]

/-- Complete interval computation for depth 12, residue 1385. -/
theorem bounds_12_1385 : exactInterval 12 1385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1385 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1385) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1385 : oddCount 1385 12 = 6 ∧ acceleratedOrbit 12 1385 = 247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1385 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1385) = 3 ^ 6 * m + 247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1385.1, data_12_1385.2]

/-- Complete interval computation for depth 12, residue 1386. -/
theorem bounds_12_1386 : exactInterval 12 1386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1386 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1386) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1386 : oddCount 1386 12 = 4 ∧ acceleratedOrbit 12 1386 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1386 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1386) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1386.1, data_12_1386.2]

/-- Complete interval computation for depth 12, residue 1387. -/
theorem bounds_12_1387 : exactInterval 12 1387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1387 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1387) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1387 : oddCount 1387 12 = 7 ∧ acceleratedOrbit 12 1387 = 742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1387 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1387) = 3 ^ 7 * m + 742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1387.1, data_12_1387.2]

/-- Complete interval computation for depth 12, residue 1388. -/
theorem bounds_12_1388 : exactInterval 12 1388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1388 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1388) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1388 : oddCount 1388 12 = 6 ∧ acceleratedOrbit 12 1388 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1388 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1388) = 3 ^ 6 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1388.1, data_12_1388.2]

/-- Complete interval computation for depth 12, residue 1389. -/
theorem bounds_12_1389 : exactInterval 12 1389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1389 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1389) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1389 : oddCount 1389 12 = 6 ∧ acceleratedOrbit 12 1389 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1389 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1389) = 3 ^ 6 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1389.1, data_12_1389.2]

/-- Complete interval computation for depth 12, residue 1390. -/
theorem bounds_12_1390 : exactInterval 12 1390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1390 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1390) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1390 : oddCount 1390 12 = 6 ∧ acceleratedOrbit 12 1390 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1390 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1390) = 3 ^ 6 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1390.1, data_12_1390.2]

/-- Complete interval computation for depth 12, residue 1391. -/
theorem bounds_12_1391 : exactInterval 12 1391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1391 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1391) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1391 : oddCount 1391 12 = 8 ∧ acceleratedOrbit 12 1391 = 2231 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1391 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1391) = 3 ^ 8 * m + 2231 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1391.1, data_12_1391.2]

/-- Complete interval computation for depth 12, residue 1392. -/
theorem bounds_12_1392 : exactInterval 12 1392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1392 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1392) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1392 : oddCount 1392 12 = 4 ∧ acceleratedOrbit 12 1392 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1392 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1392) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1392.1, data_12_1392.2]

/-- Complete interval computation for depth 12, residue 1393. -/
theorem bounds_12_1393 : exactInterval 12 1393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1393 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1393) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1393 : oddCount 1393 12 = 4 ∧ acceleratedOrbit 12 1393 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1393 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1393) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1393.1, data_12_1393.2]

/-- Complete interval computation for depth 12, residue 1394. -/
theorem bounds_12_1394 : exactInterval 12 1394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1394 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1394) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1394 : oddCount 1394 12 = 5 ∧ acceleratedOrbit 12 1394 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1394 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1394) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1394.1, data_12_1394.2]

/-- Complete interval computation for depth 12, residue 1395. -/
theorem bounds_12_1395 : exactInterval 12 1395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1395 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1395) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1395 : oddCount 1395 12 = 5 ∧ acceleratedOrbit 12 1395 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1395 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1395) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1395.1, data_12_1395.2]

/-- Complete interval computation for depth 12, residue 1396. -/
theorem bounds_12_1396 : exactInterval 12 1396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1396 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1396) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1396 : oddCount 1396 12 = 4 ∧ acceleratedOrbit 12 1396 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1396 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1396) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1396.1, data_12_1396.2]

end Collatz.Research.StoppingAtlas.Batch0291
