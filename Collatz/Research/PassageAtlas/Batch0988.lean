import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0988

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32342. -/
theorem bounds_15_32342 : exactInterval 15 32342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32342 : oddCount 32342 15 = 8 ∧ acceleratedOrbit 15 32342 = 6479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32342) = 3 ^ 8 * m + 6479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32342.1, data_15_32342.2]

/-- Complete interval computation for depth 15, residue 32343. -/
theorem bounds_15_32343 : exactInterval 15 32343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32343 : oddCount 32343 15 = 8 ∧ acceleratedOrbit 15 32343 = 6479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32343) = 3 ^ 8 * m + 6479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32343.1, data_15_32343.2]

/-- Complete interval computation for depth 15, residue 32344. -/
theorem bounds_15_32344 : exactInterval 15 32344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32344 : oddCount 32344 15 = 4 ∧ acceleratedOrbit 15 32344 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32344) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32344.1, data_15_32344.2]

/-- Complete interval computation for depth 15, residue 32345. -/
theorem bounds_15_32345 : exactInterval 15 32345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32345 : oddCount 32345 15 = 9 ∧ acceleratedOrbit 15 32345 = 19433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32345) = 3 ^ 9 * m + 19433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32345.1, data_15_32345.2]

/-- Complete interval computation for depth 15, residue 32346. -/
theorem bounds_15_32346 : exactInterval 15 32346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32346 : oddCount 32346 15 = 4 ∧ acceleratedOrbit 15 32346 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32346) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32346.1, data_15_32346.2]

/-- Complete interval computation for depth 15, residue 32347. -/
theorem bounds_15_32347 : exactInterval 15 32347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32347 : oddCount 32347 15 = 7 ∧ acceleratedOrbit 15 32347 = 2159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32347) = 3 ^ 7 * m + 2159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32347.1, data_15_32347.2]

/-- Complete interval computation for depth 15, residue 32348. -/
theorem bounds_15_32348 : exactInterval 15 32348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32348 : oddCount 32348 15 = 4 ∧ acceleratedOrbit 15 32348 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32348) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32348.1, data_15_32348.2]

/-- Complete interval computation for depth 15, residue 32349. -/
theorem bounds_15_32349 : exactInterval 15 32349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32349 : oddCount 32349 15 = 4 ∧ acceleratedOrbit 15 32349 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32349) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32349.1, data_15_32349.2]

/-- Complete interval computation for depth 15, residue 32350. -/
theorem bounds_15_32350 : exactInterval 15 32350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32350 : oddCount 32350 15 = 8 ∧ acceleratedOrbit 15 32350 = 6479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32350) = 3 ^ 8 * m + 6479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32350.1, data_15_32350.2]

/-- Complete interval computation for depth 15, residue 32351. -/
theorem bounds_15_32351 : exactInterval 15 32351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32351 : oddCount 32351 15 = 8 ∧ acceleratedOrbit 15 32351 = 6479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32351) = 3 ^ 8 * m + 6479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32351.1, data_15_32351.2]

/-- Complete interval computation for depth 15, residue 32352. -/
theorem bounds_15_32352 : exactInterval 15 32352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32352 : oddCount 32352 15 = 6 ∧ acceleratedOrbit 15 32352 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32352) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32352.1, data_15_32352.2]

/-- Complete interval computation for depth 15, residue 32353. -/
theorem bounds_15_32353 : exactInterval 15 32353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32353 : oddCount 32353 15 = 9 ∧ acceleratedOrbit 15 32353 = 19439 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32353) = 3 ^ 9 * m + 19439 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32353.1, data_15_32353.2]

/-- Complete interval computation for depth 15, residue 32354. -/
theorem bounds_15_32354 : exactInterval 15 32354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32354 : oddCount 32354 15 = 4 ∧ acceleratedOrbit 15 32354 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32354) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32354.1, data_15_32354.2]

/-- Complete interval computation for depth 15, residue 32355. -/
theorem bounds_15_32355 : exactInterval 15 32355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32355 : oddCount 32355 15 = 4 ∧ acceleratedOrbit 15 32355 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32355) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32355.1, data_15_32355.2]

/-- Complete interval computation for depth 15, residue 32356. -/
theorem bounds_15_32356 : exactInterval 15 32356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32356 : oddCount 32356 15 = 4 ∧ acceleratedOrbit 15 32356 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32356) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32356.1, data_15_32356.2]

/-- Complete interval computation for depth 15, residue 32357. -/
theorem bounds_15_32357 : exactInterval 15 32357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32357 : oddCount 32357 15 = 4 ∧ acceleratedOrbit 15 32357 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32357) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32357.1, data_15_32357.2]

/-- Complete interval computation for depth 15, residue 32358. -/
theorem bounds_15_32358 : exactInterval 15 32358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32358 : oddCount 32358 15 = 4 ∧ acceleratedOrbit 15 32358 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32358) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32358.1, data_15_32358.2]

/-- Complete interval computation for depth 15, residue 32359. -/
theorem bounds_15_32359 : exactInterval 15 32359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32359 : oddCount 32359 15 = 10 ∧ acceleratedOrbit 15 32359 = 58315 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32359) = 3 ^ 10 * m + 58315 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32359.1, data_15_32359.2]

/-- Complete interval computation for depth 15, residue 32360. -/
theorem bounds_15_32360 : exactInterval 15 32360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32360 : oddCount 32360 15 = 6 ∧ acceleratedOrbit 15 32360 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32360) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32360.1, data_15_32360.2]

/-- Complete interval computation for depth 15, residue 32361. -/
theorem bounds_15_32361 : exactInterval 15 32361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32361 : oddCount 32361 15 = 12 ∧ acceleratedOrbit 15 32361 = 524879 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32361) = 3 ^ 12 * m + 524879 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32361.1, data_15_32361.2]

/-- Complete interval computation for depth 15, residue 32362. -/
theorem bounds_15_32362 : exactInterval 15 32362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32362 : oddCount 32362 15 = 6 ∧ acceleratedOrbit 15 32362 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32362) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32362.1, data_15_32362.2]

/-- Complete interval computation for depth 15, residue 32363. -/
theorem bounds_15_32363 : exactInterval 15 32363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32363 : oddCount 32363 15 = 9 ∧ acceleratedOrbit 15 32363 = 19442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32363) = 3 ^ 9 * m + 19442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32363.1, data_15_32363.2]

/-- Complete interval computation for depth 15, residue 32364. -/
theorem bounds_15_32364 : exactInterval 15 32364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32364 : oddCount 32364 15 = 8 ∧ acceleratedOrbit 15 32364 = 6482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32364) = 3 ^ 8 * m + 6482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32364.1, data_15_32364.2]

/-- Complete interval computation for depth 15, residue 32365. -/
theorem bounds_15_32365 : exactInterval 15 32365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32365 : oddCount 32365 15 = 8 ∧ acceleratedOrbit 15 32365 = 6482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32365) = 3 ^ 8 * m + 6482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32365.1, data_15_32365.2]

/-- Complete interval computation for depth 15, residue 32366. -/
theorem bounds_15_32366 : exactInterval 15 32366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32366 : oddCount 32366 15 = 8 ∧ acceleratedOrbit 15 32366 = 6482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32366) = 3 ^ 8 * m + 6482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32366.1, data_15_32366.2]

/-- Complete interval computation for depth 15, residue 32367. -/
theorem bounds_15_32367 : exactInterval 15 32367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32367 : oddCount 32367 15 = 8 ∧ acceleratedOrbit 15 32367 = 6481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32367) = 3 ^ 8 * m + 6481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32367.1, data_15_32367.2]

/-- Complete interval computation for depth 15, residue 32368. -/
theorem bounds_15_32368 : exactInterval 15 32368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32368 : oddCount 32368 15 = 7 ∧ acceleratedOrbit 15 32368 = 2162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32368) = 3 ^ 7 * m + 2162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32368.1, data_15_32368.2]

/-- Complete interval computation for depth 15, residue 32369. -/
theorem bounds_15_32369 : exactInterval 15 32369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32369 : oddCount 32369 15 = 6 ∧ acceleratedOrbit 15 32369 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32369) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32369.1, data_15_32369.2]

/-- Complete interval computation for depth 15, residue 32370. -/
theorem bounds_15_32370 : exactInterval 15 32370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32370 : oddCount 32370 15 = 7 ∧ acceleratedOrbit 15 32370 = 2161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32370) = 3 ^ 7 * m + 2161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32370.1, data_15_32370.2]

/-- Complete interval computation for depth 15, residue 32371. -/
theorem bounds_15_32371 : exactInterval 15 32371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32371 : oddCount 32371 15 = 7 ∧ acceleratedOrbit 15 32371 = 2161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32371) = 3 ^ 7 * m + 2161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32371.1, data_15_32371.2]

/-- Complete interval computation for depth 15, residue 32372. -/
theorem bounds_15_32372 : exactInterval 15 32372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32372 : oddCount 32372 15 = 7 ∧ acceleratedOrbit 15 32372 = 2162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32372) = 3 ^ 7 * m + 2162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32372.1, data_15_32372.2]

/-- Complete interval computation for depth 15, residue 32373. -/
theorem bounds_15_32373 : exactInterval 15 32373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32373 : oddCount 32373 15 = 7 ∧ acceleratedOrbit 15 32373 = 2162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32373) = 3 ^ 7 * m + 2162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32373.1, data_15_32373.2]

end Collatz.Research.PassageAtlas.Batch0988
