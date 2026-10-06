import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0164

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5341. -/
theorem bounds_15_5341 : exactInterval 15 5341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5341 : oddCount 5341 15 = 10 ∧ acceleratedOrbit 15 5341 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5341) = 3 ^ 10 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5341.1, data_15_5341.2]

/-- Complete interval computation for depth 15, residue 5342. -/
theorem bounds_15_5342 : exactInterval 15 5342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5342 : oddCount 5342 15 = 10 ∧ acceleratedOrbit 15 5342 = 9632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5342) = 3 ^ 10 * m + 9632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5342.1, data_15_5342.2]

/-- Complete interval computation for depth 15, residue 5343. -/
theorem bounds_15_5343 : exactInterval 15 5343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5343 : oddCount 5343 15 = 10 ∧ acceleratedOrbit 15 5343 = 9632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5343) = 3 ^ 10 * m + 9632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5343.1, data_15_5343.2]

/-- Complete interval computation for depth 15, residue 5344. -/
theorem bounds_15_5344 : exactInterval 15 5344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5344 : oddCount 5344 15 = 8 ∧ acceleratedOrbit 15 5344 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5344) = 3 ^ 8 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5344.1, data_15_5344.2]

/-- Complete interval computation for depth 15, residue 5345. -/
theorem bounds_15_5345 : exactInterval 15 5345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5345 : oddCount 5345 15 = 11 ∧ acceleratedOrbit 15 5345 = 28910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5345) = 3 ^ 11 * m + 28910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5345.1, data_15_5345.2]

/-- Complete interval computation for depth 15, residue 5346. -/
theorem bounds_15_5346 : exactInterval 15 5346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5346 : oddCount 5346 15 = 6 ∧ acceleratedOrbit 15 5346 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5346) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5346.1, data_15_5346.2]

/-- Complete interval computation for depth 15, residue 5347. -/
theorem bounds_15_5347 : exactInterval 15 5347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5347 : oddCount 5347 15 = 6 ∧ acceleratedOrbit 15 5347 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5347) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5347.1, data_15_5347.2]

/-- Complete interval computation for depth 15, residue 5348. -/
theorem bounds_15_5348 : exactInterval 15 5348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5348 : oddCount 5348 15 = 8 ∧ acceleratedOrbit 15 5348 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5348) = 3 ^ 8 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5348.1, data_15_5348.2]

/-- Complete interval computation for depth 15, residue 5349. -/
theorem bounds_15_5349 : exactInterval 15 5349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5349 : oddCount 5349 15 = 8 ∧ acceleratedOrbit 15 5349 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5349) = 3 ^ 8 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5349.1, data_15_5349.2]

/-- Complete interval computation for depth 15, residue 5350. -/
theorem bounds_15_5350 : exactInterval 15 5350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5350 : oddCount 5350 15 = 8 ∧ acceleratedOrbit 15 5350 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5350) = 3 ^ 8 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5350.1, data_15_5350.2]

/-- Complete interval computation for depth 15, residue 5351. -/
theorem bounds_15_5351 : exactInterval 15 5351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5351 : oddCount 5351 15 = 11 ∧ acceleratedOrbit 15 5351 = 28937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5351) = 3 ^ 11 * m + 28937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5351.1, data_15_5351.2]

/-- Complete interval computation for depth 15, residue 5352. -/
theorem bounds_15_5352 : exactInterval 15 5352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5352 : oddCount 5352 15 = 8 ∧ acceleratedOrbit 15 5352 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5352) = 3 ^ 8 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5352.1, data_15_5352.2]

/-- Complete interval computation for depth 15, residue 5353. -/
theorem bounds_15_5353 : exactInterval 15 5353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5353 : oddCount 5353 15 = 8 ∧ acceleratedOrbit 15 5353 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5353) = 3 ^ 8 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5353.1, data_15_5353.2]

/-- Complete interval computation for depth 15, residue 5354. -/
theorem bounds_15_5354 : exactInterval 15 5354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5354 : oddCount 5354 15 = 8 ∧ acceleratedOrbit 15 5354 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5354) = 3 ^ 8 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5354.1, data_15_5354.2]

/-- Complete interval computation for depth 15, residue 5355. -/
theorem bounds_15_5355 : exactInterval 15 5355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5355 : oddCount 5355 15 = 9 ∧ acceleratedOrbit 15 5355 = 3218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5355) = 3 ^ 9 * m + 3218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5355.1, data_15_5355.2]

/-- Complete interval computation for depth 15, residue 5356. -/
theorem bounds_15_5356 : exactInterval 15 5356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5356 : oddCount 5356 15 = 5 ∧ acceleratedOrbit 15 5356 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5356) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5356.1, data_15_5356.2]

/-- Complete interval computation for depth 15, residue 5357. -/
theorem bounds_15_5357 : exactInterval 15 5357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5357 : oddCount 5357 15 = 5 ∧ acceleratedOrbit 15 5357 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5357) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5357.1, data_15_5357.2]

/-- Complete interval computation for depth 15, residue 5358. -/
theorem bounds_15_5358 : exactInterval 15 5358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5358 : oddCount 5358 15 = 5 ∧ acceleratedOrbit 15 5358 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5358) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5358.1, data_15_5358.2]

/-- Complete interval computation for depth 15, residue 5359. -/
theorem bounds_15_5359 : exactInterval 15 5359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5359 : oddCount 5359 15 = 12 ∧ acceleratedOrbit 15 5359 = 86933 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5359) = 3 ^ 12 * m + 86933 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5359.1, data_15_5359.2]

/-- Complete interval computation for depth 15, residue 5360. -/
theorem bounds_15_5360 : exactInterval 15 5360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5360 : oddCount 5360 15 = 8 ∧ acceleratedOrbit 15 5360 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5360) = 3 ^ 8 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5360.1, data_15_5360.2]

/-- Complete interval computation for depth 15, residue 5361. -/
theorem bounds_15_5361 : exactInterval 15 5361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5361 : oddCount 5361 15 = 8 ∧ acceleratedOrbit 15 5361 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5361) = 3 ^ 8 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5361.1, data_15_5361.2]

/-- Complete interval computation for depth 15, residue 5362. -/
theorem bounds_15_5362 : exactInterval 15 5362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5362 : oddCount 5362 15 = 8 ∧ acceleratedOrbit 15 5362 = 1075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5362) = 3 ^ 8 * m + 1075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5362.1, data_15_5362.2]

/-- Complete interval computation for depth 15, residue 5363. -/
theorem bounds_15_5363 : exactInterval 15 5363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5363 : oddCount 5363 15 = 8 ∧ acceleratedOrbit 15 5363 = 1075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5363) = 3 ^ 8 * m + 1075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5363.1, data_15_5363.2]

/-- Complete interval computation for depth 15, residue 5364. -/
theorem bounds_15_5364 : exactInterval 15 5364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5364 : oddCount 5364 15 = 8 ∧ acceleratedOrbit 15 5364 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5364) = 3 ^ 8 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5364.1, data_15_5364.2]

/-- Complete interval computation for depth 15, residue 5365. -/
theorem bounds_15_5365 : exactInterval 15 5365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5365 : oddCount 5365 15 = 8 ∧ acceleratedOrbit 15 5365 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5365) = 3 ^ 8 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5365.1, data_15_5365.2]

/-- Complete interval computation for depth 15, residue 5366. -/
theorem bounds_15_5366 : exactInterval 15 5366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5366 : oddCount 5366 15 = 7 ∧ acceleratedOrbit 15 5366 = 359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5366) = 3 ^ 7 * m + 359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5366.1, data_15_5366.2]

/-- Complete interval computation for depth 15, residue 5367. -/
theorem bounds_15_5367 : exactInterval 15 5367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5367 : oddCount 5367 15 = 7 ∧ acceleratedOrbit 15 5367 = 359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5367) = 3 ^ 7 * m + 359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5367.1, data_15_5367.2]

/-- Complete interval computation for depth 15, residue 5368. -/
theorem bounds_15_5368 : exactInterval 15 5368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5368 : oddCount 5368 15 = 9 ∧ acceleratedOrbit 15 5368 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5368) = 3 ^ 9 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5368.1, data_15_5368.2]

/-- Complete interval computation for depth 15, residue 5369. -/
theorem bounds_15_5369 : exactInterval 15 5369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5369 : oddCount 5369 15 = 7 ∧ acceleratedOrbit 15 5369 = 359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5369) = 3 ^ 7 * m + 359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5369.1, data_15_5369.2]

/-- Complete interval computation for depth 15, residue 5370. -/
theorem bounds_15_5370 : exactInterval 15 5370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5370 : oddCount 5370 15 = 9 ∧ acceleratedOrbit 15 5370 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5370) = 3 ^ 9 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5370.1, data_15_5370.2]

/-- Complete interval computation for depth 15, residue 5371. -/
theorem bounds_15_5371 : exactInterval 15 5371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5371 : oddCount 5371 15 = 10 ∧ acceleratedOrbit 15 5371 = 9683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5371) = 3 ^ 10 * m + 9683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5371.1, data_15_5371.2]

/-- Complete interval computation for depth 15, residue 5372. -/
theorem bounds_15_5372 : exactInterval 15 5372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5372 : oddCount 5372 15 = 9 ∧ acceleratedOrbit 15 5372 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5372) = 3 ^ 9 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5372.1, data_15_5372.2]

end Collatz.Research.PassageAtlas.Batch0164
