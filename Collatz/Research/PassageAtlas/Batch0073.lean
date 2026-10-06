import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0073

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2359. -/
theorem bounds_15_2359 : exactInterval 15 2359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2359 : oddCount 2359 15 = 10 ∧ acceleratedOrbit 15 2359 = 4256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2359) = 3 ^ 10 * m + 4256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2359.1, data_15_2359.2]

/-- Complete interval computation for depth 15, residue 2360. -/
theorem bounds_15_2360 : exactInterval 15 2360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2360 : oddCount 2360 15 = 8 ∧ acceleratedOrbit 15 2360 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2360) = 3 ^ 8 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2360.1, data_15_2360.2]

/-- Complete interval computation for depth 15, residue 2361. -/
theorem bounds_15_2361 : exactInterval 15 2361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2361 : oddCount 2361 15 = 9 ∧ acceleratedOrbit 15 2361 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2361) = 3 ^ 9 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2361.1, data_15_2361.2]

/-- Complete interval computation for depth 15, residue 2362. -/
theorem bounds_15_2362 : exactInterval 15 2362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2362 : oddCount 2362 15 = 8 ∧ acceleratedOrbit 15 2362 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2362) = 3 ^ 8 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2362.1, data_15_2362.2]

/-- Complete interval computation for depth 15, residue 2363. -/
theorem bounds_15_2363 : exactInterval 15 2363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2363 : oddCount 2363 15 = 8 ∧ acceleratedOrbit 15 2363 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2363) = 3 ^ 8 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2363.1, data_15_2363.2]

/-- Complete interval computation for depth 15, residue 2364. -/
theorem bounds_15_2364 : exactInterval 15 2364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2364 : oddCount 2364 15 = 8 ∧ acceleratedOrbit 15 2364 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2364) = 3 ^ 8 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2364.1, data_15_2364.2]

/-- Complete interval computation for depth 15, residue 2365. -/
theorem bounds_15_2365 : exactInterval 15 2365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2365 : oddCount 2365 15 = 8 ∧ acceleratedOrbit 15 2365 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2365) = 3 ^ 8 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2365.1, data_15_2365.2]

/-- Complete interval computation for depth 15, residue 2366. -/
theorem bounds_15_2366 : exactInterval 15 2366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2366 : oddCount 2366 15 = 10 ∧ acceleratedOrbit 15 2366 = 4268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2366) = 3 ^ 10 * m + 4268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2366.1, data_15_2366.2]

/-- Complete interval computation for depth 15, residue 2367. -/
theorem bounds_15_2367 : exactInterval 15 2367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2367 : oddCount 2367 15 = 10 ∧ acceleratedOrbit 15 2367 = 4268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2367) = 3 ^ 10 * m + 4268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2367.1, data_15_2367.2]

/-- Complete interval computation for depth 15, residue 2368. -/
theorem bounds_15_2368 : exactInterval 15 2368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2368 : oddCount 2368 15 = 5 ∧ acceleratedOrbit 15 2368 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2368) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2368.1, data_15_2368.2]

/-- Complete interval computation for depth 15, residue 2369. -/
theorem bounds_15_2369 : exactInterval 15 2369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2369 : oddCount 2369 15 = 7 ∧ acceleratedOrbit 15 2369 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2369) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2369.1, data_15_2369.2]

/-- Complete interval computation for depth 15, residue 2370. -/
theorem bounds_15_2370 : exactInterval 15 2370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2370 : oddCount 2370 15 = 10 ∧ acceleratedOrbit 15 2370 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2370) = 3 ^ 10 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2370.1, data_15_2370.2]

/-- Complete interval computation for depth 15, residue 2371. -/
theorem bounds_15_2371 : exactInterval 15 2371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2371 : oddCount 2371 15 = 10 ∧ acceleratedOrbit 15 2371 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2371) = 3 ^ 10 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2371.1, data_15_2371.2]

/-- Complete interval computation for depth 15, residue 2372. -/
theorem bounds_15_2372 : exactInterval 15 2372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2372 : oddCount 2372 15 = 8 ∧ acceleratedOrbit 15 2372 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2372) = 3 ^ 8 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2372.1, data_15_2372.2]

/-- Complete interval computation for depth 15, residue 2373. -/
theorem bounds_15_2373 : exactInterval 15 2373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2373 : oddCount 2373 15 = 8 ∧ acceleratedOrbit 15 2373 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2373) = 3 ^ 8 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2373.1, data_15_2373.2]

/-- Complete interval computation for depth 15, residue 2374. -/
theorem bounds_15_2374 : exactInterval 15 2374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2374 : oddCount 2374 15 = 8 ∧ acceleratedOrbit 15 2374 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2374) = 3 ^ 8 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2374.1, data_15_2374.2]

/-- Complete interval computation for depth 15, residue 2375. -/
theorem bounds_15_2375 : exactInterval 15 2375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2375 : oddCount 2375 15 = 12 ∧ acceleratedOrbit 15 2375 = 38546 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2375) = 3 ^ 12 * m + 38546 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2375.1, data_15_2375.2]

/-- Complete interval computation for depth 15, residue 2376. -/
theorem bounds_15_2376 : exactInterval 15 2376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2376 : oddCount 2376 15 = 8 ∧ acceleratedOrbit 15 2376 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2376) = 3 ^ 8 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2376.1, data_15_2376.2]

/-- Complete interval computation for depth 15, residue 2377. -/
theorem bounds_15_2377 : exactInterval 15 2377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2377 : oddCount 2377 15 = 10 ∧ acceleratedOrbit 15 2377 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2377) = 3 ^ 10 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2377.1, data_15_2377.2]

/-- Complete interval computation for depth 15, residue 2378. -/
theorem bounds_15_2378 : exactInterval 15 2378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2378 : oddCount 2378 15 = 8 ∧ acceleratedOrbit 15 2378 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2378) = 3 ^ 8 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2378.1, data_15_2378.2]

/-- Complete interval computation for depth 15, residue 2379. -/
theorem bounds_15_2379 : exactInterval 15 2379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2379 : oddCount 2379 15 = 8 ∧ acceleratedOrbit 15 2379 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2379) = 3 ^ 8 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2379.1, data_15_2379.2]

/-- Complete interval computation for depth 15, residue 2380. -/
theorem bounds_15_2380 : exactInterval 15 2380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2380 : oddCount 2380 15 = 8 ∧ acceleratedOrbit 15 2380 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2380) = 3 ^ 8 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2380.1, data_15_2380.2]

/-- Complete interval computation for depth 15, residue 2381. -/
theorem bounds_15_2381 : exactInterval 15 2381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2381 : oddCount 2381 15 = 8 ∧ acceleratedOrbit 15 2381 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2381) = 3 ^ 8 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2381.1, data_15_2381.2]

/-- Complete interval computation for depth 15, residue 2382. -/
theorem bounds_15_2382 : exactInterval 15 2382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2382 : oddCount 2382 15 = 9 ∧ acceleratedOrbit 15 2382 = 1433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2382) = 3 ^ 9 * m + 1433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2382.1, data_15_2382.2]

/-- Complete interval computation for depth 15, residue 2383. -/
theorem bounds_15_2383 : exactInterval 15 2383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2383 : oddCount 2383 15 = 9 ∧ acceleratedOrbit 15 2383 = 1433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2383) = 3 ^ 9 * m + 1433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2383.1, data_15_2383.2]

/-- Complete interval computation for depth 15, residue 2384. -/
theorem bounds_15_2384 : exactInterval 15 2384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2384 : oddCount 2384 15 = 5 ∧ acceleratedOrbit 15 2384 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2384) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2384.1, data_15_2384.2]

/-- Complete interval computation for depth 15, residue 2385. -/
theorem bounds_15_2385 : exactInterval 15 2385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2385 : oddCount 2385 15 = 10 ∧ acceleratedOrbit 15 2385 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2385) = 3 ^ 10 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2385.1, data_15_2385.2]

/-- Complete interval computation for depth 15, residue 2386. -/
theorem bounds_15_2386 : exactInterval 15 2386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2386 : oddCount 2386 15 = 10 ∧ acceleratedOrbit 15 2386 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2386) = 3 ^ 10 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2386.1, data_15_2386.2]

/-- Complete interval computation for depth 15, residue 2387. -/
theorem bounds_15_2387 : exactInterval 15 2387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2387 : oddCount 2387 15 = 10 ∧ acceleratedOrbit 15 2387 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2387) = 3 ^ 10 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2387.1, data_15_2387.2]

/-- Complete interval computation for depth 15, residue 2388. -/
theorem bounds_15_2388 : exactInterval 15 2388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2388 : oddCount 2388 15 = 5 ∧ acceleratedOrbit 15 2388 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2388) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2388.1, data_15_2388.2]

/-- Complete interval computation for depth 15, residue 2389. -/
theorem bounds_15_2389 : exactInterval 15 2389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2389 : oddCount 2389 15 = 5 ∧ acceleratedOrbit 15 2389 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2389) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2389.1, data_15_2389.2]

/-- Complete interval computation for depth 15, residue 2390. -/
theorem bounds_15_2390 : exactInterval 15 2390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2390 : oddCount 2390 15 = 7 ∧ acceleratedOrbit 15 2390 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2390) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2390.1, data_15_2390.2]

/-- Complete interval computation for depth 15, residue 2391. -/
theorem bounds_15_2391 : exactInterval 15 2391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2391 : oddCount 2391 15 = 7 ∧ acceleratedOrbit 15 2391 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2391) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2391.1, data_15_2391.2]

end Collatz.Research.PassageAtlas.Batch0073
