import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0530

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17334. -/
theorem bounds_15_17334 : exactInterval 15 17334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17334 : oddCount 17334 15 = 8 ∧ acceleratedOrbit 15 17334 = 3473 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17334) = 3 ^ 8 * m + 3473 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17334.1, data_15_17334.2]

/-- Complete interval computation for depth 15, residue 17335. -/
theorem bounds_15_17335 : exactInterval 15 17335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17335 : oddCount 17335 15 = 8 ∧ acceleratedOrbit 15 17335 = 3473 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17335) = 3 ^ 8 * m + 3473 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17335.1, data_15_17335.2]

/-- Complete interval computation for depth 15, residue 17336. -/
theorem bounds_15_17336 : exactInterval 15 17336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17336 : oddCount 17336 15 = 7 ∧ acceleratedOrbit 15 17336 = 1160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17336) = 3 ^ 7 * m + 1160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17336.1, data_15_17336.2]

/-- Complete interval computation for depth 15, residue 17337. -/
theorem bounds_15_17337 : exactInterval 15 17337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17337 : oddCount 17337 15 = 8 ∧ acceleratedOrbit 15 17337 = 3473 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17337) = 3 ^ 8 * m + 3473 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17337.1, data_15_17337.2]

/-- Complete interval computation for depth 15, residue 17338. -/
theorem bounds_15_17338 : exactInterval 15 17338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17338 : oddCount 17338 15 = 7 ∧ acceleratedOrbit 15 17338 = 1160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17338) = 3 ^ 7 * m + 1160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17338.1, data_15_17338.2]

/-- Complete interval computation for depth 15, residue 17339. -/
theorem bounds_15_17339 : exactInterval 15 17339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17339 : oddCount 17339 15 = 8 ∧ acceleratedOrbit 15 17339 = 3473 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17339) = 3 ^ 8 * m + 3473 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17339.1, data_15_17339.2]

/-- Complete interval computation for depth 15, residue 17340. -/
theorem bounds_15_17340 : exactInterval 15 17340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17340 : oddCount 17340 15 = 10 ∧ acceleratedOrbit 15 17340 = 31256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17340) = 3 ^ 10 * m + 31256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17340.1, data_15_17340.2]

/-- Complete interval computation for depth 15, residue 17341. -/
theorem bounds_15_17341 : exactInterval 15 17341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17341 : oddCount 17341 15 = 10 ∧ acceleratedOrbit 15 17341 = 31256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17341) = 3 ^ 10 * m + 31256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17341.1, data_15_17341.2]

/-- Complete interval computation for depth 15, residue 17342. -/
theorem bounds_15_17342 : exactInterval 15 17342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17342 : oddCount 17342 15 = 10 ∧ acceleratedOrbit 15 17342 = 31256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17342) = 3 ^ 10 * m + 31256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17342.1, data_15_17342.2]

/-- Complete interval computation for depth 15, residue 17343. -/
theorem bounds_15_17343 : exactInterval 15 17343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17343 : oddCount 17343 15 = 11 ∧ acceleratedOrbit 15 17343 = 93764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17343) = 3 ^ 11 * m + 93764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17343.1, data_15_17343.2]

/-- Complete interval computation for depth 15, residue 17344. -/
theorem bounds_15_17344 : exactInterval 15 17344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17344 : oddCount 17344 15 = 4 ∧ acceleratedOrbit 15 17344 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17344) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17344.1, data_15_17344.2]

/-- Complete interval computation for depth 15, residue 17345. -/
theorem bounds_15_17345 : exactInterval 15 17345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17345 : oddCount 17345 15 = 6 ∧ acceleratedOrbit 15 17345 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17345) = 3 ^ 6 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17345.1, data_15_17345.2]

/-- Complete interval computation for depth 15, residue 17346. -/
theorem bounds_15_17346 : exactInterval 15 17346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17346 : oddCount 17346 15 = 6 ∧ acceleratedOrbit 15 17346 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17346) = 3 ^ 6 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17346.1, data_15_17346.2]

/-- Complete interval computation for depth 15, residue 17347. -/
theorem bounds_15_17347 : exactInterval 15 17347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17347 : oddCount 17347 15 = 6 ∧ acceleratedOrbit 15 17347 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17347) = 3 ^ 6 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17347.1, data_15_17347.2]

/-- Complete interval computation for depth 15, residue 17348. -/
theorem bounds_15_17348 : exactInterval 15 17348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17348 : oddCount 17348 15 = 4 ∧ acceleratedOrbit 15 17348 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17348) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17348.1, data_15_17348.2]

/-- Complete interval computation for depth 15, residue 17349. -/
theorem bounds_15_17349 : exactInterval 15 17349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17349 : oddCount 17349 15 = 4 ∧ acceleratedOrbit 15 17349 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17349) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17349.1, data_15_17349.2]

/-- Complete interval computation for depth 15, residue 17350. -/
theorem bounds_15_17350 : exactInterval 15 17350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17350 : oddCount 17350 15 = 4 ∧ acceleratedOrbit 15 17350 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17350) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17350.1, data_15_17350.2]

/-- Complete interval computation for depth 15, residue 17351. -/
theorem bounds_15_17351 : exactInterval 15 17351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17351 : oddCount 17351 15 = 9 ∧ acceleratedOrbit 15 17351 = 10424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17351) = 3 ^ 9 * m + 10424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17351.1, data_15_17351.2]

/-- Complete interval computation for depth 15, residue 17352. -/
theorem bounds_15_17352 : exactInterval 15 17352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17352 : oddCount 17352 15 = 8 ∧ acceleratedOrbit 15 17352 = 3478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17352) = 3 ^ 8 * m + 3478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17352.1, data_15_17352.2]

/-- Complete interval computation for depth 15, residue 17353. -/
theorem bounds_15_17353 : exactInterval 15 17353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17353 : oddCount 17353 15 = 8 ∧ acceleratedOrbit 15 17353 = 3476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17353) = 3 ^ 8 * m + 3476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17353.1, data_15_17353.2]

/-- Complete interval computation for depth 15, residue 17354. -/
theorem bounds_15_17354 : exactInterval 15 17354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17354 : oddCount 17354 15 = 8 ∧ acceleratedOrbit 15 17354 = 3478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17354) = 3 ^ 8 * m + 3478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17354.1, data_15_17354.2]

/-- Complete interval computation for depth 15, residue 17355. -/
theorem bounds_15_17355 : exactInterval 15 17355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17355 : oddCount 17355 15 = 7 ∧ acceleratedOrbit 15 17355 = 1160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17355) = 3 ^ 7 * m + 1160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17355.1, data_15_17355.2]

/-- Complete interval computation for depth 15, residue 17356. -/
theorem bounds_15_17356 : exactInterval 15 17356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17356 : oddCount 17356 15 = 8 ∧ acceleratedOrbit 15 17356 = 3478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17356) = 3 ^ 8 * m + 3478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17356.1, data_15_17356.2]

/-- Complete interval computation for depth 15, residue 17357. -/
theorem bounds_15_17357 : exactInterval 15 17357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17357 : oddCount 17357 15 = 8 ∧ acceleratedOrbit 15 17357 = 3478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17357) = 3 ^ 8 * m + 3478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17357.1, data_15_17357.2]

/-- Complete interval computation for depth 15, residue 17358. -/
theorem bounds_15_17358 : exactInterval 15 17358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17358 : oddCount 17358 15 = 10 ∧ acceleratedOrbit 15 17358 = 31286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17358) = 3 ^ 10 * m + 31286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17358.1, data_15_17358.2]

/-- Complete interval computation for depth 15, residue 17359. -/
theorem bounds_15_17359 : exactInterval 15 17359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17359 : oddCount 17359 15 = 10 ∧ acceleratedOrbit 15 17359 = 31286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17359) = 3 ^ 10 * m + 31286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17359.1, data_15_17359.2]

/-- Complete interval computation for depth 15, residue 17360. -/
theorem bounds_15_17360 : exactInterval 15 17360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17360 : oddCount 17360 15 = 4 ∧ acceleratedOrbit 15 17360 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17360) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17360.1, data_15_17360.2]

/-- Complete interval computation for depth 15, residue 17361. -/
theorem bounds_15_17361 : exactInterval 15 17361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17361 : oddCount 17361 15 = 8 ∧ acceleratedOrbit 15 17361 = 3478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17361) = 3 ^ 8 * m + 3478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17361.1, data_15_17361.2]

/-- Complete interval computation for depth 15, residue 17362. -/
theorem bounds_15_17362 : exactInterval 15 17362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17362 : oddCount 17362 15 = 7 ∧ acceleratedOrbit 15 17362 = 1159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17362) = 3 ^ 7 * m + 1159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17362.1, data_15_17362.2]

/-- Complete interval computation for depth 15, residue 17363. -/
theorem bounds_15_17363 : exactInterval 15 17363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17363 : oddCount 17363 15 = 7 ∧ acceleratedOrbit 15 17363 = 1159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17363) = 3 ^ 7 * m + 1159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17363.1, data_15_17363.2]

/-- Complete interval computation for depth 15, residue 17364. -/
theorem bounds_15_17364 : exactInterval 15 17364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17364 : oddCount 17364 15 = 4 ∧ acceleratedOrbit 15 17364 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17364) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17364.1, data_15_17364.2]

/-- Complete interval computation for depth 15, residue 17365. -/
theorem bounds_15_17365 : exactInterval 15 17365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17365 : oddCount 17365 15 = 4 ∧ acceleratedOrbit 15 17365 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17365) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17365.1, data_15_17365.2]

/-- Complete interval computation for depth 15, residue 17366. -/
theorem bounds_15_17366 : exactInterval 15 17366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17366 : oddCount 17366 15 = 11 ∧ acceleratedOrbit 15 17366 = 93905 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17366) = 3 ^ 11 * m + 93905 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17366.1, data_15_17366.2]

end Collatz.Research.PassageAtlas.Batch0530
