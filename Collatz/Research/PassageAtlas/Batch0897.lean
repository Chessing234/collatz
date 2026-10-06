import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0897

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29360. -/
theorem bounds_15_29360 : exactInterval 15 29360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29360 : oddCount 29360 15 = 5 ∧ acceleratedOrbit 15 29360 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29360) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29360.1, data_15_29360.2]

/-- Complete interval computation for depth 15, residue 29361. -/
theorem bounds_15_29361 : exactInterval 15 29361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29361 : oddCount 29361 15 = 7 ∧ acceleratedOrbit 15 29361 = 1961 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29361) = 3 ^ 7 * m + 1961 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29361.1, data_15_29361.2]

/-- Complete interval computation for depth 15, residue 29362. -/
theorem bounds_15_29362 : exactInterval 15 29362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29362 : oddCount 29362 15 = 7 ∧ acceleratedOrbit 15 29362 = 1961 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29362) = 3 ^ 7 * m + 1961 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29362.1, data_15_29362.2]

/-- Complete interval computation for depth 15, residue 29363. -/
theorem bounds_15_29363 : exactInterval 15 29363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29363 : oddCount 29363 15 = 7 ∧ acceleratedOrbit 15 29363 = 1961 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29363) = 3 ^ 7 * m + 1961 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29363.1, data_15_29363.2]

/-- Complete interval computation for depth 15, residue 29364. -/
theorem bounds_15_29364 : exactInterval 15 29364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29364 : oddCount 29364 15 = 5 ∧ acceleratedOrbit 15 29364 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29364) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29364.1, data_15_29364.2]

/-- Complete interval computation for depth 15, residue 29365. -/
theorem bounds_15_29365 : exactInterval 15 29365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29365 : oddCount 29365 15 = 5 ∧ acceleratedOrbit 15 29365 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29365) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29365.1, data_15_29365.2]

/-- Complete interval computation for depth 15, residue 29366. -/
theorem bounds_15_29366 : exactInterval 15 29366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29366 : oddCount 29366 15 = 8 ∧ acceleratedOrbit 15 29366 = 5881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29366) = 3 ^ 8 * m + 5881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29366.1, data_15_29366.2]

/-- Complete interval computation for depth 15, residue 29367. -/
theorem bounds_15_29367 : exactInterval 15 29367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29367 : oddCount 29367 15 = 8 ∧ acceleratedOrbit 15 29367 = 5881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29367) = 3 ^ 8 * m + 5881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29367.1, data_15_29367.2]

/-- Complete interval computation for depth 15, residue 29368. -/
theorem bounds_15_29368 : exactInterval 15 29368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29368 : oddCount 29368 15 = 5 ∧ acceleratedOrbit 15 29368 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29368) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29368.1, data_15_29368.2]

/-- Complete interval computation for depth 15, residue 29369. -/
theorem bounds_15_29369 : exactInterval 15 29369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29369 : oddCount 29369 15 = 7 ∧ acceleratedOrbit 15 29369 = 1961 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29369) = 3 ^ 7 * m + 1961 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29369.1, data_15_29369.2]

/-- Complete interval computation for depth 15, residue 29370. -/
theorem bounds_15_29370 : exactInterval 15 29370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29370 : oddCount 29370 15 = 5 ∧ acceleratedOrbit 15 29370 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29370) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29370.1, data_15_29370.2]

/-- Complete interval computation for depth 15, residue 29371. -/
theorem bounds_15_29371 : exactInterval 15 29371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29371 : oddCount 29371 15 = 10 ∧ acceleratedOrbit 15 29371 = 52933 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29371) = 3 ^ 10 * m + 52933 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29371.1, data_15_29371.2]

/-- Complete interval computation for depth 15, residue 29372. -/
theorem bounds_15_29372 : exactInterval 15 29372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29372 : oddCount 29372 15 = 9 ∧ acceleratedOrbit 15 29372 = 17648 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29372) = 3 ^ 9 * m + 17648 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29372.1, data_15_29372.2]

/-- Complete interval computation for depth 15, residue 29373. -/
theorem bounds_15_29373 : exactInterval 15 29373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29373 : oddCount 29373 15 = 9 ∧ acceleratedOrbit 15 29373 = 17648 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29373) = 3 ^ 9 * m + 17648 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29373.1, data_15_29373.2]

/-- Complete interval computation for depth 15, residue 29374. -/
theorem bounds_15_29374 : exactInterval 15 29374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29374 : oddCount 29374 15 = 9 ∧ acceleratedOrbit 15 29374 = 17648 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29374) = 3 ^ 9 * m + 17648 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29374.1, data_15_29374.2]

/-- Complete interval computation for depth 15, residue 29375. -/
theorem bounds_15_29375 : exactInterval 15 29375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29375 : oddCount 29375 15 = 12 ∧ acceleratedOrbit 15 29375 = 476432 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29375) = 3 ^ 12 * m + 476432 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29375.1, data_15_29375.2]

/-- Complete interval computation for depth 15, residue 29376. -/
theorem bounds_15_29376 : exactInterval 15 29376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29376 : oddCount 29376 15 = 4 ∧ acceleratedOrbit 15 29376 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29376) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29376.1, data_15_29376.2]

/-- Complete interval computation for depth 15, residue 29377. -/
theorem bounds_15_29377 : exactInterval 15 29377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29377 : oddCount 29377 15 = 5 ∧ acceleratedOrbit 15 29377 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29377) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29377.1, data_15_29377.2]

/-- Complete interval computation for depth 15, residue 29378. -/
theorem bounds_15_29378 : exactInterval 15 29378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29378 : oddCount 29378 15 = 9 ∧ acceleratedOrbit 15 29378 = 17651 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29378) = 3 ^ 9 * m + 17651 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29378.1, data_15_29378.2]

/-- Complete interval computation for depth 15, residue 29379. -/
theorem bounds_15_29379 : exactInterval 15 29379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29379 : oddCount 29379 15 = 9 ∧ acceleratedOrbit 15 29379 = 17651 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29379) = 3 ^ 9 * m + 17651 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29379.1, data_15_29379.2]

/-- Complete interval computation for depth 15, residue 29380. -/
theorem bounds_15_29380 : exactInterval 15 29380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29380 : oddCount 29380 15 = 7 ∧ acceleratedOrbit 15 29380 = 1964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29380) = 3 ^ 7 * m + 1964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29380.1, data_15_29380.2]

/-- Complete interval computation for depth 15, residue 29381. -/
theorem bounds_15_29381 : exactInterval 15 29381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29381 : oddCount 29381 15 = 7 ∧ acceleratedOrbit 15 29381 = 1964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29381) = 3 ^ 7 * m + 1964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29381.1, data_15_29381.2]

/-- Complete interval computation for depth 15, residue 29382. -/
theorem bounds_15_29382 : exactInterval 15 29382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29382 : oddCount 29382 15 = 7 ∧ acceleratedOrbit 15 29382 = 1964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29382) = 3 ^ 7 * m + 1964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29382.1, data_15_29382.2]

/-- Complete interval computation for depth 15, residue 29383. -/
theorem bounds_15_29383 : exactInterval 15 29383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29383 : oddCount 29383 15 = 8 ∧ acceleratedOrbit 15 29383 = 5885 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29383) = 3 ^ 8 * m + 5885 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29383.1, data_15_29383.2]

/-- Complete interval computation for depth 15, residue 29384. -/
theorem bounds_15_29384 : exactInterval 15 29384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29384 : oddCount 29384 15 = 7 ∧ acceleratedOrbit 15 29384 = 1964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29384) = 3 ^ 7 * m + 1964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29384.1, data_15_29384.2]

/-- Complete interval computation for depth 15, residue 29385. -/
theorem bounds_15_29385 : exactInterval 15 29385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29385 : oddCount 29385 15 = 9 ∧ acceleratedOrbit 15 29385 = 17657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29385) = 3 ^ 9 * m + 17657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29385.1, data_15_29385.2]

/-- Complete interval computation for depth 15, residue 29386. -/
theorem bounds_15_29386 : exactInterval 15 29386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29386 : oddCount 29386 15 = 7 ∧ acceleratedOrbit 15 29386 = 1964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29386) = 3 ^ 7 * m + 1964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29386.1, data_15_29386.2]

/-- Complete interval computation for depth 15, residue 29387. -/
theorem bounds_15_29387 : exactInterval 15 29387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29387 : oddCount 29387 15 = 9 ∧ acceleratedOrbit 15 29387 = 17657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29387) = 3 ^ 9 * m + 17657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29387.1, data_15_29387.2]

/-- Complete interval computation for depth 15, residue 29388. -/
theorem bounds_15_29388 : exactInterval 15 29388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29388 : oddCount 29388 15 = 7 ∧ acceleratedOrbit 15 29388 = 1964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29388) = 3 ^ 7 * m + 1964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29388.1, data_15_29388.2]

/-- Complete interval computation for depth 15, residue 29389. -/
theorem bounds_15_29389 : exactInterval 15 29389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29389 : oddCount 29389 15 = 7 ∧ acceleratedOrbit 15 29389 = 1964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29389) = 3 ^ 7 * m + 1964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29389.1, data_15_29389.2]

/-- Complete interval computation for depth 15, residue 29390. -/
theorem bounds_15_29390 : exactInterval 15 29390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29390 : oddCount 29390 15 = 10 ∧ acceleratedOrbit 15 29390 = 52967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29390) = 3 ^ 10 * m + 52967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29390.1, data_15_29390.2]

/-- Complete interval computation for depth 15, residue 29391. -/
theorem bounds_15_29391 : exactInterval 15 29391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29391 : oddCount 29391 15 = 10 ∧ acceleratedOrbit 15 29391 = 52967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29391) = 3 ^ 10 * m + 52967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29391.1, data_15_29391.2]

end Collatz.Research.PassageAtlas.Batch0897
