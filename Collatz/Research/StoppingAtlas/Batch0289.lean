import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0289

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1351. -/
theorem bounds_12_1351 : exactInterval 12 1351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1351 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1351) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1351 : oddCount 1351 12 = 9 ∧ acceleratedOrbit 12 1351 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1351 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1351) = 3 ^ 9 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1351.1, data_12_1351.2]

/-- Complete interval computation for depth 12, residue 1352. -/
theorem bounds_12_1352 : exactInterval 12 1352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1352 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1352) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1352 : oddCount 1352 12 = 8 ∧ acceleratedOrbit 12 1352 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1352 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1352) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1352.1, data_12_1352.2]

/-- Complete interval computation for depth 12, residue 1353. -/
theorem bounds_12_1353 : exactInterval 12 1353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1353 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1353) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1353 : oddCount 1353 12 = 7 ∧ acceleratedOrbit 12 1353 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1353 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1353) = 3 ^ 7 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1353.1, data_12_1353.2]

/-- Complete interval computation for depth 12, residue 1354. -/
theorem bounds_12_1354 : exactInterval 12 1354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1354 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1354) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1354 : oddCount 1354 12 = 8 ∧ acceleratedOrbit 12 1354 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1354 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1354) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1354.1, data_12_1354.2]

/-- Complete interval computation for depth 12, residue 1355. -/
theorem bounds_12_1355 : exactInterval 12 1355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1355 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1355) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1355 : oddCount 1355 12 = 7 ∧ acceleratedOrbit 12 1355 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1355 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1355) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1355.1, data_12_1355.2]

/-- Complete interval computation for depth 12, residue 1356. -/
theorem bounds_12_1356 : exactInterval 12 1356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1356 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1356) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1356 : oddCount 1356 12 = 8 ∧ acceleratedOrbit 12 1356 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1356 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1356) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1356.1, data_12_1356.2]

/-- Complete interval computation for depth 12, residue 1357. -/
theorem bounds_12_1357 : exactInterval 12 1357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1357 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1357) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1357 : oddCount 1357 12 = 8 ∧ acceleratedOrbit 12 1357 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1357 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1357) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1357.1, data_12_1357.2]

/-- Complete interval computation for depth 12, residue 1358. -/
theorem bounds_12_1358 : exactInterval 12 1358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1358 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1358) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1358 : oddCount 1358 12 = 8 ∧ acceleratedOrbit 12 1358 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1358 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1358) = 3 ^ 8 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1358.1, data_12_1358.2]

/-- Complete interval computation for depth 12, residue 1359. -/
theorem bounds_12_1359 : exactInterval 12 1359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1359 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1359) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1359 : oddCount 1359 12 = 8 ∧ acceleratedOrbit 12 1359 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1359 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1359) = 3 ^ 8 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1359.1, data_12_1359.2]

/-- Complete interval computation for depth 12, residue 1360. -/
theorem bounds_12_1360 : exactInterval 12 1360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1360 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1360) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1360 : oddCount 1360 12 = 1 ∧ acceleratedOrbit 12 1360 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1360 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1360) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1360.1, data_12_1360.2]

/-- Complete interval computation for depth 12, residue 1361. -/
theorem bounds_12_1361 : exactInterval 12 1361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1361 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1361) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1361 : oddCount 1361 12 = 9 ∧ acceleratedOrbit 12 1361 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1361 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1361) = 3 ^ 9 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1361.1, data_12_1361.2]

/-- Complete interval computation for depth 12, residue 1362. -/
theorem bounds_12_1362 : exactInterval 12 1362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1362 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1362) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1362 : oddCount 1362 12 = 10 ∧ acceleratedOrbit 12 1362 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1362 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1362) = 3 ^ 10 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1362.1, data_12_1362.2]

/-- Complete interval computation for depth 12, residue 1363. -/
theorem bounds_12_1363 : exactInterval 12 1363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1363 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1363) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1363 : oddCount 1363 12 = 10 ∧ acceleratedOrbit 12 1363 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1363 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1363) = 3 ^ 10 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1363.1, data_12_1363.2]

/-- Complete interval computation for depth 12, residue 1364. -/
theorem bounds_12_1364 : exactInterval 12 1364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1364 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1364) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1364 : oddCount 1364 12 = 1 ∧ acceleratedOrbit 12 1364 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1364 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1364) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1364.1, data_12_1364.2]

/-- Complete interval computation for depth 12, residue 1365. -/
theorem bounds_12_1365 : exactInterval 12 1365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1365 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1365) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1365 : oddCount 1365 12 = 1 ∧ acceleratedOrbit 12 1365 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1365 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1365) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1365.1, data_12_1365.2]

/-- Complete interval computation for depth 12, residue 1366. -/
theorem bounds_12_1366 : exactInterval 12 1366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1366 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1366) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1366 : oddCount 1366 12 = 6 ∧ acceleratedOrbit 12 1366 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1366 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1366) = 3 ^ 6 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1366.1, data_12_1366.2]

end Collatz.Research.StoppingAtlas.Batch0289
