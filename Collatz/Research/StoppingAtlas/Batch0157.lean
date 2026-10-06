import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0157

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1372. -/
theorem bounds_11_1372 : exactInterval 11 1372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1372 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1372) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1372 : oddCount 1372 11 = 5 ∧ acceleratedOrbit 11 1372 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1372 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1372) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1372.1, data_11_1372.2]

/-- Complete interval computation for depth 11, residue 1373. -/
theorem bounds_11_1373 : exactInterval 11 1373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1373 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1373) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1373 : oddCount 1373 11 = 5 ∧ acceleratedOrbit 11 1373 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1373 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1373) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1373.1, data_11_1373.2]

/-- Complete interval computation for depth 11, residue 1374. -/
theorem bounds_11_1374 : exactInterval 11 1374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1374 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1374) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1374 : oddCount 1374 11 = 6 ∧ acceleratedOrbit 11 1374 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1374 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1374) = 3 ^ 6 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1374.1, data_11_1374.2]

/-- Complete interval computation for depth 11, residue 1375. -/
theorem bounds_11_1375 : exactInterval 11 1375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1375 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1375) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1375 : oddCount 1375 11 = 6 ∧ acceleratedOrbit 11 1375 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1375 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1375) = 3 ^ 6 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1375.1, data_11_1375.2]

/-- Complete interval computation for depth 11, residue 1376. -/
theorem bounds_11_1376 : exactInterval 11 1376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1376 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1376) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1376 : oddCount 1376 11 = 4 ∧ acceleratedOrbit 11 1376 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1376 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1376) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1376.1, data_11_1376.2]

/-- Complete interval computation for depth 11, residue 1377. -/
theorem bounds_11_1377 : exactInterval 11 1377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1377 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1377) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1377 : oddCount 1377 11 = 6 ∧ acceleratedOrbit 11 1377 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1377 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1377) = 3 ^ 6 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1377.1, data_11_1377.2]

/-- Complete interval computation for depth 11, residue 1378. -/
theorem bounds_11_1378 : exactInterval 11 1378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1378 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1378) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1378 : oddCount 1378 11 = 4 ∧ acceleratedOrbit 11 1378 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1378 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1378) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1378.1, data_11_1378.2]

/-- Complete interval computation for depth 11, residue 1379. -/
theorem bounds_11_1379 : exactInterval 11 1379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1379 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1379) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1379 : oddCount 1379 11 = 4 ∧ acceleratedOrbit 11 1379 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1379 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1379) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1379.1, data_11_1379.2]

/-- Complete interval computation for depth 11, residue 1380. -/
theorem bounds_11_1380 : exactInterval 11 1380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1380 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1380) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1380 : oddCount 1380 11 = 4 ∧ acceleratedOrbit 11 1380 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1380 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1380) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1380.1, data_11_1380.2]

/-- Complete interval computation for depth 11, residue 1381. -/
theorem bounds_11_1381 : exactInterval 11 1381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1381 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1381) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1381 : oddCount 1381 11 = 4 ∧ acceleratedOrbit 11 1381 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1381 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1381) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1381.1, data_11_1381.2]

/-- Complete interval computation for depth 11, residue 1382. -/
theorem bounds_11_1382 : exactInterval 11 1382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1382 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1382) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1382 : oddCount 1382 11 = 4 ∧ acceleratedOrbit 11 1382 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1382 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1382) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1382.1, data_11_1382.2]

/-- Complete interval computation for depth 11, residue 1383. -/
theorem bounds_11_1383 : exactInterval 11 1383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1383 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1383) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1383 : oddCount 1383 11 = 9 ∧ acceleratedOrbit 11 1383 = 13304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1383 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1383) = 3 ^ 9 * m + 13304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1383.1, data_11_1383.2]

/-- Complete interval computation for depth 11, residue 1384. -/
theorem bounds_11_1384 : exactInterval 11 1384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1384 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1384) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1384 : oddCount 1384 11 = 4 ∧ acceleratedOrbit 11 1384 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1384 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1384) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1384.1, data_11_1384.2]

/-- Complete interval computation for depth 11, residue 1385. -/
theorem bounds_11_1385 : exactInterval 11 1385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1385 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1385) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1385 : oddCount 1385 11 = 6 ∧ acceleratedOrbit 11 1385 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1385 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1385) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1385.1, data_11_1385.2]

/-- Complete interval computation for depth 11, residue 1386. -/
theorem bounds_11_1386 : exactInterval 11 1386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1386 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1386) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1386 : oddCount 1386 11 = 4 ∧ acceleratedOrbit 11 1386 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1386 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1386) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1386.1, data_11_1386.2]

end Collatz.Research.StoppingAtlas.Batch0157
