import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0561

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18350. -/
theorem bounds_15_18350 : exactInterval 15 18350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18350 : oddCount 18350 15 = 9 ∧ acceleratedOrbit 15 18350 = 11026 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18350) = 3 ^ 9 * m + 11026 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18350.1, data_15_18350.2]

/-- Complete interval computation for depth 15, residue 18351. -/
theorem bounds_15_18351 : exactInterval 15 18351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18351 : oddCount 18351 15 = 7 ∧ acceleratedOrbit 15 18351 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18351) = 3 ^ 7 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18351.1, data_15_18351.2]

/-- Complete interval computation for depth 15, residue 18352. -/
theorem bounds_15_18352 : exactInterval 15 18352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18352 : oddCount 18352 15 = 6 ∧ acceleratedOrbit 15 18352 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18352) = 3 ^ 6 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18352.1, data_15_18352.2]

/-- Complete interval computation for depth 15, residue 18353. -/
theorem bounds_15_18353 : exactInterval 15 18353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18353 : oddCount 18353 15 = 5 ∧ acceleratedOrbit 15 18353 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18353) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18353.1, data_15_18353.2]

/-- Complete interval computation for depth 15, residue 18354. -/
theorem bounds_15_18354 : exactInterval 15 18354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18354 : oddCount 18354 15 = 5 ∧ acceleratedOrbit 15 18354 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18354) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18354.1, data_15_18354.2]

/-- Complete interval computation for depth 15, residue 18355. -/
theorem bounds_15_18355 : exactInterval 15 18355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18355 : oddCount 18355 15 = 5 ∧ acceleratedOrbit 15 18355 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18355) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18355.1, data_15_18355.2]

/-- Complete interval computation for depth 15, residue 18356. -/
theorem bounds_15_18356 : exactInterval 15 18356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18356 : oddCount 18356 15 = 6 ∧ acceleratedOrbit 15 18356 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18356) = 3 ^ 6 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18356.1, data_15_18356.2]

/-- Complete interval computation for depth 15, residue 18357. -/
theorem bounds_15_18357 : exactInterval 15 18357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18357 : oddCount 18357 15 = 6 ∧ acceleratedOrbit 15 18357 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18357) = 3 ^ 6 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18357.1, data_15_18357.2]

/-- Complete interval computation for depth 15, residue 18358. -/
theorem bounds_15_18358 : exactInterval 15 18358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18358 : oddCount 18358 15 = 7 ∧ acceleratedOrbit 15 18358 = 1226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18358) = 3 ^ 7 * m + 1226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18358.1, data_15_18358.2]

/-- Complete interval computation for depth 15, residue 18359. -/
theorem bounds_15_18359 : exactInterval 15 18359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18359 : oddCount 18359 15 = 7 ∧ acceleratedOrbit 15 18359 = 1226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18359) = 3 ^ 7 * m + 1226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18359.1, data_15_18359.2]

/-- Complete interval computation for depth 15, residue 18360. -/
theorem bounds_15_18360 : exactInterval 15 18360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18360 : oddCount 18360 15 = 6 ∧ acceleratedOrbit 15 18360 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18360) = 3 ^ 6 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18360.1, data_15_18360.2]

/-- Complete interval computation for depth 15, residue 18361. -/
theorem bounds_15_18361 : exactInterval 15 18361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18361 : oddCount 18361 15 = 7 ∧ acceleratedOrbit 15 18361 = 1226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18361) = 3 ^ 7 * m + 1226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18361.1, data_15_18361.2]

/-- Complete interval computation for depth 15, residue 18362. -/
theorem bounds_15_18362 : exactInterval 15 18362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18362 : oddCount 18362 15 = 6 ∧ acceleratedOrbit 15 18362 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18362) = 3 ^ 6 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18362.1, data_15_18362.2]

/-- Complete interval computation for depth 15, residue 18363. -/
theorem bounds_15_18363 : exactInterval 15 18363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18363 : oddCount 18363 15 = 7 ∧ acceleratedOrbit 15 18363 = 1226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18363) = 3 ^ 7 * m + 1226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18363.1, data_15_18363.2]

/-- Complete interval computation for depth 15, residue 18364. -/
theorem bounds_15_18364 : exactInterval 15 18364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18364 : oddCount 18364 15 = 11 ∧ acceleratedOrbit 15 18364 = 99305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18364) = 3 ^ 11 * m + 99305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18364.1, data_15_18364.2]

/-- Complete interval computation for depth 15, residue 18365. -/
theorem bounds_15_18365 : exactInterval 15 18365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18365 : oddCount 18365 15 = 11 ∧ acceleratedOrbit 15 18365 = 99305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18365) = 3 ^ 11 * m + 99305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18365.1, data_15_18365.2]

/-- Complete interval computation for depth 15, residue 18366. -/
theorem bounds_15_18366 : exactInterval 15 18366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18366 : oddCount 18366 15 = 11 ∧ acceleratedOrbit 15 18366 = 99305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18366) = 3 ^ 11 * m + 99305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18366.1, data_15_18366.2]

/-- Complete interval computation for depth 15, residue 18367. -/
theorem bounds_15_18367 : exactInterval 15 18367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18367 : oddCount 18367 15 = 10 ∧ acceleratedOrbit 15 18367 = 33101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18367) = 3 ^ 10 * m + 33101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18367.1, data_15_18367.2]

/-- Complete interval computation for depth 15, residue 18368. -/
theorem bounds_15_18368 : exactInterval 15 18368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18368 : oddCount 18368 15 = 6 ∧ acceleratedOrbit 15 18368 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18368) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18368.1, data_15_18368.2]

/-- Complete interval computation for depth 15, residue 18369. -/
theorem bounds_15_18369 : exactInterval 15 18369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18369 : oddCount 18369 15 = 6 ∧ acceleratedOrbit 15 18369 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18369) = 3 ^ 6 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18369.1, data_15_18369.2]

/-- Complete interval computation for depth 15, residue 18370. -/
theorem bounds_15_18370 : exactInterval 15 18370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18370 : oddCount 18370 15 = 9 ∧ acceleratedOrbit 15 18370 = 11038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18370) = 3 ^ 9 * m + 11038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18370.1, data_15_18370.2]

/-- Complete interval computation for depth 15, residue 18371. -/
theorem bounds_15_18371 : exactInterval 15 18371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18371 : oddCount 18371 15 = 9 ∧ acceleratedOrbit 15 18371 = 11038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18371) = 3 ^ 9 * m + 11038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18371.1, data_15_18371.2]

/-- Complete interval computation for depth 15, residue 18372. -/
theorem bounds_15_18372 : exactInterval 15 18372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18372 : oddCount 18372 15 = 5 ∧ acceleratedOrbit 15 18372 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18372) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18372.1, data_15_18372.2]

/-- Complete interval computation for depth 15, residue 18373. -/
theorem bounds_15_18373 : exactInterval 15 18373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18373 : oddCount 18373 15 = 5 ∧ acceleratedOrbit 15 18373 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18373) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18373.1, data_15_18373.2]

/-- Complete interval computation for depth 15, residue 18374. -/
theorem bounds_15_18374 : exactInterval 15 18374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18374 : oddCount 18374 15 = 5 ∧ acceleratedOrbit 15 18374 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18374) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18374.1, data_15_18374.2]

/-- Complete interval computation for depth 15, residue 18375. -/
theorem bounds_15_18375 : exactInterval 15 18375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18375 : oddCount 18375 15 = 8 ∧ acceleratedOrbit 15 18375 = 3680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18375) = 3 ^ 8 * m + 3680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18375.1, data_15_18375.2]

/-- Complete interval computation for depth 15, residue 18376. -/
theorem bounds_15_18376 : exactInterval 15 18376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18376 : oddCount 18376 15 = 7 ∧ acceleratedOrbit 15 18376 = 1228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18376) = 3 ^ 7 * m + 1228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18376.1, data_15_18376.2]

/-- Complete interval computation for depth 15, residue 18377. -/
theorem bounds_15_18377 : exactInterval 15 18377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18377 : oddCount 18377 15 = 9 ∧ acceleratedOrbit 15 18377 = 11042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18377) = 3 ^ 9 * m + 11042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18377.1, data_15_18377.2]

/-- Complete interval computation for depth 15, residue 18378. -/
theorem bounds_15_18378 : exactInterval 15 18378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18378 : oddCount 18378 15 = 7 ∧ acceleratedOrbit 15 18378 = 1228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18378) = 3 ^ 7 * m + 1228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18378.1, data_15_18378.2]

/-- Complete interval computation for depth 15, residue 18379. -/
theorem bounds_15_18379 : exactInterval 15 18379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18379 : oddCount 18379 15 = 7 ∧ acceleratedOrbit 15 18379 = 1228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18379) = 3 ^ 7 * m + 1228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18379.1, data_15_18379.2]

/-- Complete interval computation for depth 15, residue 18380. -/
theorem bounds_15_18380 : exactInterval 15 18380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18380 : oddCount 18380 15 = 7 ∧ acceleratedOrbit 15 18380 = 1228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18380) = 3 ^ 7 * m + 1228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18380.1, data_15_18380.2]

/-- Complete interval computation for depth 15, residue 18381. -/
theorem bounds_15_18381 : exactInterval 15 18381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18381 : oddCount 18381 15 = 7 ∧ acceleratedOrbit 15 18381 = 1228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18381) = 3 ^ 7 * m + 1228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18381.1, data_15_18381.2]

end Collatz.Research.PassageAtlas.Batch0561
