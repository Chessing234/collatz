import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0156

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1356. -/
theorem bounds_11_1356 : exactInterval 11 1356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1356 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1356) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1356 : oddCount 1356 11 = 7 ∧ acceleratedOrbit 11 1356 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1356 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1356) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1356.1, data_11_1356.2]

/-- Complete interval computation for depth 11, residue 1357. -/
theorem bounds_11_1357 : exactInterval 11 1357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1357 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1357) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1357 : oddCount 1357 11 = 7 ∧ acceleratedOrbit 11 1357 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1357 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1357) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1357.1, data_11_1357.2]

/-- Complete interval computation for depth 11, residue 1358. -/
theorem bounds_11_1358 : exactInterval 11 1358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1358 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1358) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1358 : oddCount 1358 11 = 7 ∧ acceleratedOrbit 11 1358 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1358 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1358) = 3 ^ 7 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1358.1, data_11_1358.2]

/-- Complete interval computation for depth 11, residue 1359. -/
theorem bounds_11_1359 : exactInterval 11 1359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1359 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1359) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1359 : oddCount 1359 11 = 7 ∧ acceleratedOrbit 11 1359 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1359 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1359) = 3 ^ 7 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1359.1, data_11_1359.2]

/-- Complete interval computation for depth 11, residue 1360. -/
theorem bounds_11_1360 : exactInterval 11 1360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1360 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1360) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1360 : oddCount 1360 11 = 1 ∧ acceleratedOrbit 11 1360 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1360 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1360) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1360.1, data_11_1360.2]

/-- Complete interval computation for depth 11, residue 1361. -/
theorem bounds_11_1361 : exactInterval 11 1361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1361 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1361) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1361 : oddCount 1361 11 = 8 ∧ acceleratedOrbit 11 1361 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1361 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1361) = 3 ^ 8 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1361.1, data_11_1361.2]

/-- Complete interval computation for depth 11, residue 1362. -/
theorem bounds_11_1362 : exactInterval 11 1362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1362 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1362) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1362 : oddCount 1362 11 = 9 ∧ acceleratedOrbit 11 1362 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1362 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1362) = 3 ^ 9 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1362.1, data_11_1362.2]

/-- Complete interval computation for depth 11, residue 1363. -/
theorem bounds_11_1363 : exactInterval 11 1363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1363 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1363) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1363 : oddCount 1363 11 = 9 ∧ acceleratedOrbit 11 1363 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1363 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1363) = 3 ^ 9 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1363.1, data_11_1363.2]

/-- Complete interval computation for depth 11, residue 1364. -/
theorem bounds_11_1364 : exactInterval 11 1364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1364 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1364) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1364 : oddCount 1364 11 = 1 ∧ acceleratedOrbit 11 1364 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1364 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1364) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1364.1, data_11_1364.2]

/-- Complete interval computation for depth 11, residue 1365. -/
theorem bounds_11_1365 : exactInterval 11 1365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1365 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1365) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1365 : oddCount 1365 11 = 1 ∧ acceleratedOrbit 11 1365 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1365 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1365) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1365.1, data_11_1365.2]

/-- Complete interval computation for depth 11, residue 1366. -/
theorem bounds_11_1366 : exactInterval 11 1366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1366 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1366) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1366 : oddCount 1366 11 = 6 ∧ acceleratedOrbit 11 1366 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1366 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1366) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1366.1, data_11_1366.2]

/-- Complete interval computation for depth 11, residue 1367. -/
theorem bounds_11_1367 : exactInterval 11 1367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1367 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1367) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1367 : oddCount 1367 11 = 6 ∧ acceleratedOrbit 11 1367 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1367 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1367) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1367.1, data_11_1367.2]

/-- Complete interval computation for depth 11, residue 1368. -/
theorem bounds_11_1368 : exactInterval 11 1368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1368 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1368) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1368 : oddCount 1368 11 = 5 ∧ acceleratedOrbit 11 1368 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1368 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1368) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1368.1, data_11_1368.2]

/-- Complete interval computation for depth 11, residue 1369. -/
theorem bounds_11_1369 : exactInterval 11 1369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1369 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1369) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1369 : oddCount 1369 11 = 5 ∧ acceleratedOrbit 11 1369 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1369 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1369) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1369.1, data_11_1369.2]

/-- Complete interval computation for depth 11, residue 1370. -/
theorem bounds_11_1370 : exactInterval 11 1370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1370 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1370) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1370 : oddCount 1370 11 = 5 ∧ acceleratedOrbit 11 1370 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1370 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1370) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1370.1, data_11_1370.2]

/-- Complete interval computation for depth 11, residue 1371. -/
theorem bounds_11_1371 : exactInterval 11 1371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1371 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1371) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1371 : oddCount 1371 11 = 7 ∧ acceleratedOrbit 11 1371 = 1466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1371 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1371) = 3 ^ 7 * m + 1466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1371.1, data_11_1371.2]

end Collatz.Research.StoppingAtlas.Batch0156
