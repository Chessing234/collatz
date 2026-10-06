import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0317

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10354. -/
theorem bounds_15_10354 : exactInterval 15 10354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10354 : oddCount 10354 15 = 7 ∧ acceleratedOrbit 15 10354 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10354) = 3 ^ 7 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10354.1, data_15_10354.2]

/-- Complete interval computation for depth 15, residue 10355. -/
theorem bounds_15_10355 : exactInterval 15 10355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10355 : oddCount 10355 15 = 7 ∧ acceleratedOrbit 15 10355 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10355) = 3 ^ 7 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10355.1, data_15_10355.2]

/-- Complete interval computation for depth 15, residue 10356. -/
theorem bounds_15_10356 : exactInterval 15 10356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10356 : oddCount 10356 15 = 5 ∧ acceleratedOrbit 15 10356 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10356) = 3 ^ 5 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10356.1, data_15_10356.2]

/-- Complete interval computation for depth 15, residue 10357. -/
theorem bounds_15_10357 : exactInterval 15 10357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10357 : oddCount 10357 15 = 5 ∧ acceleratedOrbit 15 10357 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10357) = 3 ^ 5 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10357.1, data_15_10357.2]

/-- Complete interval computation for depth 15, residue 10358. -/
theorem bounds_15_10358 : exactInterval 15 10358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10358 : oddCount 10358 15 = 9 ∧ acceleratedOrbit 15 10358 = 6227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10358) = 3 ^ 9 * m + 6227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10358.1, data_15_10358.2]

/-- Complete interval computation for depth 15, residue 10359. -/
theorem bounds_15_10359 : exactInterval 15 10359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10359 : oddCount 10359 15 = 9 ∧ acceleratedOrbit 15 10359 = 6227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10359) = 3 ^ 9 * m + 6227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10359.1, data_15_10359.2]

/-- Complete interval computation for depth 15, residue 10360. -/
theorem bounds_15_10360 : exactInterval 15 10360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10360 : oddCount 10360 15 = 5 ∧ acceleratedOrbit 15 10360 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10360) = 3 ^ 5 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10360.1, data_15_10360.2]

/-- Complete interval computation for depth 15, residue 10361. -/
theorem bounds_15_10361 : exactInterval 15 10361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10361 : oddCount 10361 15 = 8 ∧ acceleratedOrbit 15 10361 = 2075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10361) = 3 ^ 8 * m + 2075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10361.1, data_15_10361.2]

/-- Complete interval computation for depth 15, residue 10362. -/
theorem bounds_15_10362 : exactInterval 15 10362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10362 : oddCount 10362 15 = 5 ∧ acceleratedOrbit 15 10362 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10362) = 3 ^ 5 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10362.1, data_15_10362.2]

/-- Complete interval computation for depth 15, residue 10363. -/
theorem bounds_15_10363 : exactInterval 15 10363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10363 : oddCount 10363 15 = 9 ∧ acceleratedOrbit 15 10363 = 6227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10363) = 3 ^ 9 * m + 6227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10363.1, data_15_10363.2]

/-- Complete interval computation for depth 15, residue 10364. -/
theorem bounds_15_10364 : exactInterval 15 10364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10364 : oddCount 10364 15 = 7 ∧ acceleratedOrbit 15 10364 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10364) = 3 ^ 7 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10364.1, data_15_10364.2]

/-- Complete interval computation for depth 15, residue 10365. -/
theorem bounds_15_10365 : exactInterval 15 10365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10365 : oddCount 10365 15 = 7 ∧ acceleratedOrbit 15 10365 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10365) = 3 ^ 7 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10365.1, data_15_10365.2]

/-- Complete interval computation for depth 15, residue 10366. -/
theorem bounds_15_10366 : exactInterval 15 10366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10366 : oddCount 10366 15 = 7 ∧ acceleratedOrbit 15 10366 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10366) = 3 ^ 7 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10366.1, data_15_10366.2]

/-- Complete interval computation for depth 15, residue 10367. -/
theorem bounds_15_10367 : exactInterval 15 10367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10367 : oddCount 10367 15 = 12 ∧ acceleratedOrbit 15 10367 = 168155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10367) = 3 ^ 12 * m + 168155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10367.1, data_15_10367.2]

/-- Complete interval computation for depth 15, residue 10368. -/
theorem bounds_15_10368 : exactInterval 15 10368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10368 : oddCount 10368 15 = 5 ∧ acceleratedOrbit 15 10368 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10368) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10368.1, data_15_10368.2]

/-- Complete interval computation for depth 15, residue 10369. -/
theorem bounds_15_10369 : exactInterval 15 10369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10369 : oddCount 10369 15 = 8 ∧ acceleratedOrbit 15 10369 = 2078 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10369) = 3 ^ 8 * m + 2078 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10369.1, data_15_10369.2]

/-- Complete interval computation for depth 15, residue 10370. -/
theorem bounds_15_10370 : exactInterval 15 10370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10370 : oddCount 10370 15 = 5 ∧ acceleratedOrbit 15 10370 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10370) = 3 ^ 5 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10370.1, data_15_10370.2]

/-- Complete interval computation for depth 15, residue 10371. -/
theorem bounds_15_10371 : exactInterval 15 10371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10371 : oddCount 10371 15 = 5 ∧ acceleratedOrbit 15 10371 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10371) = 3 ^ 5 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10371.1, data_15_10371.2]

/-- Complete interval computation for depth 15, residue 10372. -/
theorem bounds_15_10372 : exactInterval 15 10372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10372 : oddCount 10372 15 = 5 ∧ acceleratedOrbit 15 10372 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10372) = 3 ^ 5 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10372.1, data_15_10372.2]

/-- Complete interval computation for depth 15, residue 10373. -/
theorem bounds_15_10373 : exactInterval 15 10373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10373 : oddCount 10373 15 = 5 ∧ acceleratedOrbit 15 10373 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10373) = 3 ^ 5 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10373.1, data_15_10373.2]

/-- Complete interval computation for depth 15, residue 10374. -/
theorem bounds_15_10374 : exactInterval 15 10374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10374 : oddCount 10374 15 = 5 ∧ acceleratedOrbit 15 10374 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10374) = 3 ^ 5 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10374.1, data_15_10374.2]

/-- Complete interval computation for depth 15, residue 10375. -/
theorem bounds_15_10375 : exactInterval 15 10375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10375 : oddCount 10375 15 = 9 ∧ acceleratedOrbit 15 10375 = 6236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10375) = 3 ^ 9 * m + 6236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10375.1, data_15_10375.2]

/-- Complete interval computation for depth 15, residue 10376. -/
theorem bounds_15_10376 : exactInterval 15 10376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10376 : oddCount 10376 15 = 6 ∧ acceleratedOrbit 15 10376 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10376) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10376.1, data_15_10376.2]

/-- Complete interval computation for depth 15, residue 10377. -/
theorem bounds_15_10377 : exactInterval 15 10377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10377 : oddCount 10377 15 = 10 ∧ acceleratedOrbit 15 10377 = 18704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10377) = 3 ^ 10 * m + 18704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10377.1, data_15_10377.2]

/-- Complete interval computation for depth 15, residue 10378. -/
theorem bounds_15_10378 : exactInterval 15 10378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10378 : oddCount 10378 15 = 6 ∧ acceleratedOrbit 15 10378 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10378) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10378.1, data_15_10378.2]

/-- Complete interval computation for depth 15, residue 10379. -/
theorem bounds_15_10379 : exactInterval 15 10379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10379 : oddCount 10379 15 = 11 ∧ acceleratedOrbit 15 10379 = 56132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10379) = 3 ^ 11 * m + 56132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10379.1, data_15_10379.2]

/-- Complete interval computation for depth 15, residue 10380. -/
theorem bounds_15_10380 : exactInterval 15 10380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10380 : oddCount 10380 15 = 6 ∧ acceleratedOrbit 15 10380 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10380) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10380.1, data_15_10380.2]

/-- Complete interval computation for depth 15, residue 10381. -/
theorem bounds_15_10381 : exactInterval 15 10381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10381 : oddCount 10381 15 = 6 ∧ acceleratedOrbit 15 10381 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10381) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10381.1, data_15_10381.2]

/-- Complete interval computation for depth 15, residue 10382. -/
theorem bounds_15_10382 : exactInterval 15 10382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10382 : oddCount 10382 15 = 9 ∧ acceleratedOrbit 15 10382 = 6239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10382) = 3 ^ 9 * m + 6239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10382.1, data_15_10382.2]

/-- Complete interval computation for depth 15, residue 10383. -/
theorem bounds_15_10383 : exactInterval 15 10383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10383 : oddCount 10383 15 = 9 ∧ acceleratedOrbit 15 10383 = 6239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10383) = 3 ^ 9 * m + 6239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10383.1, data_15_10383.2]

/-- Complete interval computation for depth 15, residue 10384. -/
theorem bounds_15_10384 : exactInterval 15 10384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10384 : oddCount 10384 15 = 7 ∧ acceleratedOrbit 15 10384 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10384) = 3 ^ 7 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10384.1, data_15_10384.2]

/-- Complete interval computation for depth 15, residue 10385. -/
theorem bounds_15_10385 : exactInterval 15 10385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10385 : oddCount 10385 15 = 8 ∧ acceleratedOrbit 15 10385 = 2081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10385) = 3 ^ 8 * m + 2081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10385.1, data_15_10385.2]

/-- Complete interval computation for depth 15, residue 10386. -/
theorem bounds_15_10386 : exactInterval 15 10386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10386 : oddCount 10386 15 = 8 ∧ acceleratedOrbit 15 10386 = 2081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10386) = 3 ^ 8 * m + 2081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10386.1, data_15_10386.2]

end Collatz.Research.PassageAtlas.Batch0317
