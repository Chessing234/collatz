import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0290

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1367. -/
theorem bounds_12_1367 : exactInterval 12 1367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1367 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1367) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1367 : oddCount 1367 12 = 6 ∧ acceleratedOrbit 12 1367 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1367 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1367) = 3 ^ 6 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1367.1, data_12_1367.2]

/-- Complete interval computation for depth 12, residue 1368. -/
theorem bounds_12_1368 : exactInterval 12 1368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1368 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1368) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1368 : oddCount 1368 12 = 5 ∧ acceleratedOrbit 12 1368 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1368 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1368) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1368.1, data_12_1368.2]

/-- Complete interval computation for depth 12, residue 1369. -/
theorem bounds_12_1369 : exactInterval 12 1369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1369 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1369) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1369 : oddCount 1369 12 = 6 ∧ acceleratedOrbit 12 1369 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1369 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1369) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1369.1, data_12_1369.2]

/-- Complete interval computation for depth 12, residue 1370. -/
theorem bounds_12_1370 : exactInterval 12 1370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1370 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1370) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1370 : oddCount 1370 12 = 5 ∧ acceleratedOrbit 12 1370 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1370 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1370) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1370.1, data_12_1370.2]

/-- Complete interval computation for depth 12, residue 1371. -/
theorem bounds_12_1371 : exactInterval 12 1371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1371 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1371) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1371 : oddCount 1371 12 = 7 ∧ acceleratedOrbit 12 1371 = 733 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1371 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1371) = 3 ^ 7 * m + 733 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1371.1, data_12_1371.2]

/-- Complete interval computation for depth 12, residue 1372. -/
theorem bounds_12_1372 : exactInterval 12 1372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1372 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1372) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1372 : oddCount 1372 12 = 5 ∧ acceleratedOrbit 12 1372 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1372 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1372) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1372.1, data_12_1372.2]

/-- Complete interval computation for depth 12, residue 1373. -/
theorem bounds_12_1373 : exactInterval 12 1373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1373 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1373) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1373 : oddCount 1373 12 = 5 ∧ acceleratedOrbit 12 1373 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1373 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1373) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1373.1, data_12_1373.2]

/-- Complete interval computation for depth 12, residue 1374. -/
theorem bounds_12_1374 : exactInterval 12 1374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1374 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1374) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1374 : oddCount 1374 12 = 6 ∧ acceleratedOrbit 12 1374 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1374 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1374) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1374.1, data_12_1374.2]

/-- Complete interval computation for depth 12, residue 1375. -/
theorem bounds_12_1375 : exactInterval 12 1375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1375 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1375) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1375 : oddCount 1375 12 = 6 ∧ acceleratedOrbit 12 1375 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1375 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1375) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1375.1, data_12_1375.2]

/-- Complete interval computation for depth 12, residue 1376. -/
theorem bounds_12_1376 : exactInterval 12 1376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1376 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1376) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1376 : oddCount 1376 12 = 4 ∧ acceleratedOrbit 12 1376 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1376 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1376) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1376.1, data_12_1376.2]

/-- Complete interval computation for depth 12, residue 1377. -/
theorem bounds_12_1377 : exactInterval 12 1377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1377 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1377) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1377 : oddCount 1377 12 = 7 ∧ acceleratedOrbit 12 1377 = 737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1377 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1377) = 3 ^ 7 * m + 737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1377.1, data_12_1377.2]

/-- Complete interval computation for depth 12, residue 1378. -/
theorem bounds_12_1378 : exactInterval 12 1378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1378 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1378) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1378 : oddCount 1378 12 = 5 ∧ acceleratedOrbit 12 1378 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1378 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1378) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1378.1, data_12_1378.2]

/-- Complete interval computation for depth 12, residue 1379. -/
theorem bounds_12_1379 : exactInterval 12 1379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1379 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1379) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1379 : oddCount 1379 12 = 5 ∧ acceleratedOrbit 12 1379 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1379 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1379) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1379.1, data_12_1379.2]

/-- Complete interval computation for depth 12, residue 1380. -/
theorem bounds_12_1380 : exactInterval 12 1380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1380 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1380) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1380 : oddCount 1380 12 = 5 ∧ acceleratedOrbit 12 1380 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1380 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1380) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1380.1, data_12_1380.2]

/-- Complete interval computation for depth 12, residue 1381. -/
theorem bounds_12_1381 : exactInterval 12 1381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1381 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1381) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1381 : oddCount 1381 12 = 5 ∧ acceleratedOrbit 12 1381 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1381 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1381) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1381.1, data_12_1381.2]

end Collatz.Research.StoppingAtlas.Batch0290
