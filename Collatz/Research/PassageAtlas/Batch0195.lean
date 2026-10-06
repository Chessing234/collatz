import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0195

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6356. -/
theorem bounds_15_6356 : exactInterval 15 6356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6356 : oddCount 6356 15 = 4 ∧ acceleratedOrbit 15 6356 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6356) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6356.1, data_15_6356.2]

/-- Complete interval computation for depth 15, residue 6357. -/
theorem bounds_15_6357 : exactInterval 15 6357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6357 : oddCount 6357 15 = 4 ∧ acceleratedOrbit 15 6357 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6357) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6357.1, data_15_6357.2]

/-- Complete interval computation for depth 15, residue 6358. -/
theorem bounds_15_6358 : exactInterval 15 6358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6358 : oddCount 6358 15 = 8 ∧ acceleratedOrbit 15 6358 = 1274 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6358) = 3 ^ 8 * m + 1274 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6358.1, data_15_6358.2]

/-- Complete interval computation for depth 15, residue 6359. -/
theorem bounds_15_6359 : exactInterval 15 6359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6359 : oddCount 6359 15 = 8 ∧ acceleratedOrbit 15 6359 = 1274 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6359) = 3 ^ 8 * m + 1274 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6359.1, data_15_6359.2]

/-- Complete interval computation for depth 15, residue 6360. -/
theorem bounds_15_6360 : exactInterval 15 6360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6360 : oddCount 6360 15 = 9 ∧ acceleratedOrbit 15 6360 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6360) = 3 ^ 9 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6360.1, data_15_6360.2]

/-- Complete interval computation for depth 15, residue 6361. -/
theorem bounds_15_6361 : exactInterval 15 6361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6361 : oddCount 6361 15 = 9 ∧ acceleratedOrbit 15 6361 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6361) = 3 ^ 9 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6361.1, data_15_6361.2]

/-- Complete interval computation for depth 15, residue 6362. -/
theorem bounds_15_6362 : exactInterval 15 6362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6362 : oddCount 6362 15 = 9 ∧ acceleratedOrbit 15 6362 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6362) = 3 ^ 9 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6362.1, data_15_6362.2]

/-- Complete interval computation for depth 15, residue 6363. -/
theorem bounds_15_6363 : exactInterval 15 6363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6363 : oddCount 6363 15 = 9 ∧ acceleratedOrbit 15 6363 = 3824 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6363) = 3 ^ 9 * m + 3824 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6363.1, data_15_6363.2]

/-- Complete interval computation for depth 15, residue 6364. -/
theorem bounds_15_6364 : exactInterval 15 6364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6364 : oddCount 6364 15 = 9 ∧ acceleratedOrbit 15 6364 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6364) = 3 ^ 9 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6364.1, data_15_6364.2]

/-- Complete interval computation for depth 15, residue 6365. -/
theorem bounds_15_6365 : exactInterval 15 6365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6365 : oddCount 6365 15 = 9 ∧ acceleratedOrbit 15 6365 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6365) = 3 ^ 9 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6365.1, data_15_6365.2]

/-- Complete interval computation for depth 15, residue 6366. -/
theorem bounds_15_6366 : exactInterval 15 6366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6366 : oddCount 6366 15 = 10 ∧ acceleratedOrbit 15 6366 = 11477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6366) = 3 ^ 10 * m + 11477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6366.1, data_15_6366.2]

/-- Complete interval computation for depth 15, residue 6367. -/
theorem bounds_15_6367 : exactInterval 15 6367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6367 : oddCount 6367 15 = 10 ∧ acceleratedOrbit 15 6367 = 11477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6367) = 3 ^ 10 * m + 11477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6367.1, data_15_6367.2]

/-- Complete interval computation for depth 15, residue 6368. -/
theorem bounds_15_6368 : exactInterval 15 6368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6368 : oddCount 6368 15 = 6 ∧ acceleratedOrbit 15 6368 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6368) = 3 ^ 6 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6368.1, data_15_6368.2]

/-- Complete interval computation for depth 15, residue 6369. -/
theorem bounds_15_6369 : exactInterval 15 6369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6369 : oddCount 6369 15 = 11 ∧ acceleratedOrbit 15 6369 = 34445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6369) = 3 ^ 11 * m + 34445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6369.1, data_15_6369.2]

/-- Complete interval computation for depth 15, residue 6370. -/
theorem bounds_15_6370 : exactInterval 15 6370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6370 : oddCount 6370 15 = 4 ∧ acceleratedOrbit 15 6370 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6370) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6370.1, data_15_6370.2]

/-- Complete interval computation for depth 15, residue 6371. -/
theorem bounds_15_6371 : exactInterval 15 6371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6371 : oddCount 6371 15 = 4 ∧ acceleratedOrbit 15 6371 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6371) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6371.1, data_15_6371.2]

/-- Complete interval computation for depth 15, residue 6372. -/
theorem bounds_15_6372 : exactInterval 15 6372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6372 : oddCount 6372 15 = 6 ∧ acceleratedOrbit 15 6372 = 142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6372) = 3 ^ 6 * m + 142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6372.1, data_15_6372.2]

/-- Complete interval computation for depth 15, residue 6373. -/
theorem bounds_15_6373 : exactInterval 15 6373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6373 : oddCount 6373 15 = 6 ∧ acceleratedOrbit 15 6373 = 142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6373) = 3 ^ 6 * m + 142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6373.1, data_15_6373.2]

/-- Complete interval computation for depth 15, residue 6374. -/
theorem bounds_15_6374 : exactInterval 15 6374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6374 : oddCount 6374 15 = 6 ∧ acceleratedOrbit 15 6374 = 142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6374) = 3 ^ 6 * m + 142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6374.1, data_15_6374.2]

/-- Complete interval computation for depth 15, residue 6375. -/
theorem bounds_15_6375 : exactInterval 15 6375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6375 : oddCount 6375 15 = 10 ∧ acceleratedOrbit 15 6375 = 11492 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6375) = 3 ^ 10 * m + 11492 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6375.1, data_15_6375.2]

/-- Complete interval computation for depth 15, residue 6376. -/
theorem bounds_15_6376 : exactInterval 15 6376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6376 : oddCount 6376 15 = 6 ∧ acceleratedOrbit 15 6376 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6376) = 3 ^ 6 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6376.1, data_15_6376.2]

/-- Complete interval computation for depth 15, residue 6377. -/
theorem bounds_15_6377 : exactInterval 15 6377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6377 : oddCount 6377 15 = 9 ∧ acceleratedOrbit 15 6377 = 3833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6377) = 3 ^ 9 * m + 3833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6377.1, data_15_6377.2]

/-- Complete interval computation for depth 15, residue 6378. -/
theorem bounds_15_6378 : exactInterval 15 6378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6378 : oddCount 6378 15 = 6 ∧ acceleratedOrbit 15 6378 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6378) = 3 ^ 6 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6378.1, data_15_6378.2]

/-- Complete interval computation for depth 15, residue 6379. -/
theorem bounds_15_6379 : exactInterval 15 6379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6379 : oddCount 6379 15 = 10 ∧ acceleratedOrbit 15 6379 = 11501 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6379) = 3 ^ 10 * m + 11501 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6379.1, data_15_6379.2]

/-- Complete interval computation for depth 15, residue 6380. -/
theorem bounds_15_6380 : exactInterval 15 6380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6380 : oddCount 6380 15 = 7 ∧ acceleratedOrbit 15 6380 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6380) = 3 ^ 7 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6380.1, data_15_6380.2]

/-- Complete interval computation for depth 15, residue 6381. -/
theorem bounds_15_6381 : exactInterval 15 6381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6381 : oddCount 6381 15 = 7 ∧ acceleratedOrbit 15 6381 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6381) = 3 ^ 7 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6381.1, data_15_6381.2]

/-- Complete interval computation for depth 15, residue 6382. -/
theorem bounds_15_6382 : exactInterval 15 6382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6382 : oddCount 6382 15 = 7 ∧ acceleratedOrbit 15 6382 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6382) = 3 ^ 7 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6382.1, data_15_6382.2]

/-- Complete interval computation for depth 15, residue 6383. -/
theorem bounds_15_6383 : exactInterval 15 6383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6383 : oddCount 6383 15 = 11 ∧ acceleratedOrbit 15 6383 = 34514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6383) = 3 ^ 11 * m + 34514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6383.1, data_15_6383.2]

/-- Complete interval computation for depth 15, residue 6384. -/
theorem bounds_15_6384 : exactInterval 15 6384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6384 : oddCount 6384 15 = 6 ∧ acceleratedOrbit 15 6384 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6384) = 3 ^ 6 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6384.1, data_15_6384.2]

/-- Complete interval computation for depth 15, residue 6385. -/
theorem bounds_15_6385 : exactInterval 15 6385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6385 : oddCount 6385 15 = 6 ∧ acceleratedOrbit 15 6385 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6385) = 3 ^ 6 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6385.1, data_15_6385.2]

/-- Complete interval computation for depth 15, residue 6386. -/
theorem bounds_15_6386 : exactInterval 15 6386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6386 : oddCount 6386 15 = 8 ∧ acceleratedOrbit 15 6386 = 1280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6386) = 3 ^ 8 * m + 1280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6386.1, data_15_6386.2]

/-- Complete interval computation for depth 15, residue 6387. -/
theorem bounds_15_6387 : exactInterval 15 6387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6387 : oddCount 6387 15 = 8 ∧ acceleratedOrbit 15 6387 = 1280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6387) = 3 ^ 8 * m + 1280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6387.1, data_15_6387.2]

/-- Complete interval computation for depth 15, residue 6388. -/
theorem bounds_15_6388 : exactInterval 15 6388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6388 : oddCount 6388 15 = 6 ∧ acceleratedOrbit 15 6388 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6388) = 3 ^ 6 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6388.1, data_15_6388.2]

end Collatz.Research.PassageAtlas.Batch0195
