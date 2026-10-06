import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0556

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1356. -/
theorem bounds_13_1356 : exactInterval 13 1356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1356 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1356) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1356 : oddCount 1356 13 = 8 ∧ acceleratedOrbit 13 1356 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1356 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1356) = 3 ^ 8 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1356.1, data_13_1356.2]

/-- Complete interval computation for depth 13, residue 1357. -/
theorem bounds_13_1357 : exactInterval 13 1357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1357 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1357) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1357 : oddCount 1357 13 = 8 ∧ acceleratedOrbit 13 1357 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1357 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1357) = 3 ^ 8 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1357.1, data_13_1357.2]

/-- Complete interval computation for depth 13, residue 1358. -/
theorem bounds_13_1358 : exactInterval 13 1358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1358 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1358) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1358 : oddCount 1358 13 = 8 ∧ acceleratedOrbit 13 1358 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1358 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1358) = 3 ^ 8 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1358.1, data_13_1358.2]

/-- Complete interval computation for depth 13, residue 1359. -/
theorem bounds_13_1359 : exactInterval 13 1359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1359 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1359) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1359 : oddCount 1359 13 = 8 ∧ acceleratedOrbit 13 1359 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1359 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1359) = 3 ^ 8 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1359.1, data_13_1359.2]

/-- Complete interval computation for depth 13, residue 1360. -/
theorem bounds_13_1360 : exactInterval 13 1360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1360 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1360) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1360 : oddCount 1360 13 = 2 ∧ acceleratedOrbit 13 1360 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1360 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1360) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1360.1, data_13_1360.2]

/-- Complete interval computation for depth 13, residue 1361. -/
theorem bounds_13_1361 : exactInterval 13 1361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1361 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1361) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1361 : oddCount 1361 13 = 9 ∧ acceleratedOrbit 13 1361 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1361 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1361) = 3 ^ 9 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1361.1, data_13_1361.2]

/-- Complete interval computation for depth 13, residue 1362. -/
theorem bounds_13_1362 : exactInterval 13 1362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1362 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1362) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1362 : oddCount 1362 13 = 10 ∧ acceleratedOrbit 13 1362 = 9841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1362 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1362) = 3 ^ 10 * m + 9841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1362.1, data_13_1362.2]

/-- Complete interval computation for depth 13, residue 1363. -/
theorem bounds_13_1363 : exactInterval 13 1363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1363 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1363) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1363 : oddCount 1363 13 = 10 ∧ acceleratedOrbit 13 1363 = 9841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1363 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1363) = 3 ^ 10 * m + 9841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1363.1, data_13_1363.2]

/-- Complete interval computation for depth 13, residue 1364. -/
theorem bounds_13_1364 : exactInterval 13 1364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1364 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1364) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1364 : oddCount 1364 13 = 2 ∧ acceleratedOrbit 13 1364 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1364 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1364) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1364.1, data_13_1364.2]

/-- Complete interval computation for depth 13, residue 1365. -/
theorem bounds_13_1365 : exactInterval 13 1365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1365 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1365) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1365 : oddCount 1365 13 = 2 ∧ acceleratedOrbit 13 1365 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1365 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1365) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1365.1, data_13_1365.2]

/-- Complete interval computation for depth 13, residue 1366. -/
theorem bounds_13_1366 : exactInterval 13 1366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1366 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1366) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1366 : oddCount 1366 13 = 6 ∧ acceleratedOrbit 13 1366 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1366 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1366) = 3 ^ 6 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1366.1, data_13_1366.2]

/-- Complete interval computation for depth 13, residue 1367. -/
theorem bounds_13_1367 : exactInterval 13 1367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1367 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1367) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1367 : oddCount 1367 13 = 6 ∧ acceleratedOrbit 13 1367 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1367 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1367) = 3 ^ 6 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1367.1, data_13_1367.2]

/-- Complete interval computation for depth 13, residue 1368. -/
theorem bounds_13_1368 : exactInterval 13 1368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1368 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1368) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1368 : oddCount 1368 13 = 5 ∧ acceleratedOrbit 13 1368 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1368 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1368) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1368.1, data_13_1368.2]

/-- Complete interval computation for depth 13, residue 1369. -/
theorem bounds_13_1369 : exactInterval 13 1369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1369 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1369) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1369 : oddCount 1369 13 = 7 ∧ acceleratedOrbit 13 1369 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1369 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1369) = 3 ^ 7 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1369.1, data_13_1369.2]

/-- Complete interval computation for depth 13, residue 1370. -/
theorem bounds_13_1370 : exactInterval 13 1370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1370 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1370) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1370 : oddCount 1370 13 = 5 ∧ acceleratedOrbit 13 1370 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1370 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1370) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1370.1, data_13_1370.2]

/-- Complete interval computation for depth 13, residue 1371. -/
theorem bounds_13_1371 : exactInterval 13 1371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1371 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1371) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1371 : oddCount 1371 13 = 8 ∧ acceleratedOrbit 13 1371 = 1100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1371 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1371) = 3 ^ 8 * m + 1100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1371.1, data_13_1371.2]

end Collatz.Research.StoppingAtlas.Batch0556
