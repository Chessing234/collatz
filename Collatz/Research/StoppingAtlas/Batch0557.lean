import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0557

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1372. -/
theorem bounds_13_1372 : exactInterval 13 1372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1372 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1372) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1372 : oddCount 1372 13 = 5 ∧ acceleratedOrbit 13 1372 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1372 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1372) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1372.1, data_13_1372.2]

/-- Complete interval computation for depth 13, residue 1373. -/
theorem bounds_13_1373 : exactInterval 13 1373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1373 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1373) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1373 : oddCount 1373 13 = 5 ∧ acceleratedOrbit 13 1373 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1373 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1373) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1373.1, data_13_1373.2]

/-- Complete interval computation for depth 13, residue 1374. -/
theorem bounds_13_1374 : exactInterval 13 1374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1374 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1374) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1374 : oddCount 1374 13 = 7 ∧ acceleratedOrbit 13 1374 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1374 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1374) = 3 ^ 7 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1374.1, data_13_1374.2]

/-- Complete interval computation for depth 13, residue 1375. -/
theorem bounds_13_1375 : exactInterval 13 1375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1375 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1375) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1375 : oddCount 1375 13 = 7 ∧ acceleratedOrbit 13 1375 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1375 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1375) = 3 ^ 7 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1375.1, data_13_1375.2]

/-- Complete interval computation for depth 13, residue 1376. -/
theorem bounds_13_1376 : exactInterval 13 1376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1376 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1376) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1376 : oddCount 1376 13 = 4 ∧ acceleratedOrbit 13 1376 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1376 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1376) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1376.1, data_13_1376.2]

/-- Complete interval computation for depth 13, residue 1377. -/
theorem bounds_13_1377 : exactInterval 13 1377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1377 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1377) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1377 : oddCount 1377 13 = 8 ∧ acceleratedOrbit 13 1377 = 1106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1377 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1377) = 3 ^ 8 * m + 1106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1377.1, data_13_1377.2]

/-- Complete interval computation for depth 13, residue 1378. -/
theorem bounds_13_1378 : exactInterval 13 1378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1378 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1378) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1378 : oddCount 1378 13 = 6 ∧ acceleratedOrbit 13 1378 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1378 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1378) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1378.1, data_13_1378.2]

/-- Complete interval computation for depth 13, residue 1379. -/
theorem bounds_13_1379 : exactInterval 13 1379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1379 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1379) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1379 : oddCount 1379 13 = 6 ∧ acceleratedOrbit 13 1379 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1379 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1379) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1379.1, data_13_1379.2]

/-- Complete interval computation for depth 13, residue 1380. -/
theorem bounds_13_1380 : exactInterval 13 1380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1380 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1380) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1380 : oddCount 1380 13 = 6 ∧ acceleratedOrbit 13 1380 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1380 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1380) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1380.1, data_13_1380.2]

/-- Complete interval computation for depth 13, residue 1381. -/
theorem bounds_13_1381 : exactInterval 13 1381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1381 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1381) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1381 : oddCount 1381 13 = 6 ∧ acceleratedOrbit 13 1381 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1381 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1381) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1381.1, data_13_1381.2]

/-- Complete interval computation for depth 13, residue 1382. -/
theorem bounds_13_1382 : exactInterval 13 1382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1382 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1382) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1382 : oddCount 1382 13 = 6 ∧ acceleratedOrbit 13 1382 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1382 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1382) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1382.1, data_13_1382.2]

/-- Complete interval computation for depth 13, residue 1383. -/
theorem bounds_13_1383 : exactInterval 13 1383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1383 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1383) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1383 : oddCount 1383 13 = 9 ∧ acceleratedOrbit 13 1383 = 3326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1383 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1383) = 3 ^ 9 * m + 3326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1383.1, data_13_1383.2]

/-- Complete interval computation for depth 13, residue 1384. -/
theorem bounds_13_1384 : exactInterval 13 1384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1384 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1384) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1384 : oddCount 1384 13 = 4 ∧ acceleratedOrbit 13 1384 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1384 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1384) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1384.1, data_13_1384.2]

/-- Complete interval computation for depth 13, residue 1385. -/
theorem bounds_13_1385 : exactInterval 13 1385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1385 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1385) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1385 : oddCount 1385 13 = 7 ∧ acceleratedOrbit 13 1385 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1385 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1385) = 3 ^ 7 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1385.1, data_13_1385.2]

/-- Complete interval computation for depth 13, residue 1386. -/
theorem bounds_13_1386 : exactInterval 13 1386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1386 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1386) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1386 : oddCount 1386 13 = 4 ∧ acceleratedOrbit 13 1386 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1386 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1386) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1386.1, data_13_1386.2]

end Collatz.Research.StoppingAtlas.Batch0557
