import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0256

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8355. -/
theorem bounds_15_8355 : exactInterval 15 8355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8355 : oddCount 8355 15 = 5 ∧ acceleratedOrbit 15 8355 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8355) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8355.1, data_15_8355.2]

/-- Complete interval computation for depth 15, residue 8356. -/
theorem bounds_15_8356 : exactInterval 15 8356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8356 : oddCount 8356 15 = 9 ∧ acceleratedOrbit 15 8356 = 5024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8356) = 3 ^ 9 * m + 5024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8356.1, data_15_8356.2]

/-- Complete interval computation for depth 15, residue 8357. -/
theorem bounds_15_8357 : exactInterval 15 8357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8357 : oddCount 8357 15 = 9 ∧ acceleratedOrbit 15 8357 = 5024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8357) = 3 ^ 9 * m + 5024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8357.1, data_15_8357.2]

/-- Complete interval computation for depth 15, residue 8358. -/
theorem bounds_15_8358 : exactInterval 15 8358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8358 : oddCount 8358 15 = 9 ∧ acceleratedOrbit 15 8358 = 5024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8358) = 3 ^ 9 * m + 5024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8358.1, data_15_8358.2]

/-- Complete interval computation for depth 15, residue 8359. -/
theorem bounds_15_8359 : exactInterval 15 8359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8359 : oddCount 8359 15 = 13 ∧ acceleratedOrbit 15 8359 = 406781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8359) = 3 ^ 13 * m + 406781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8359.1, data_15_8359.2]

/-- Complete interval computation for depth 15, residue 8360. -/
theorem bounds_15_8360 : exactInterval 15 8360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8360 : oddCount 8360 15 = 3 ∧ acceleratedOrbit 15 8360 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8360) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8360.1, data_15_8360.2]

/-- Complete interval computation for depth 15, residue 8361. -/
theorem bounds_15_8361 : exactInterval 15 8361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8361 : oddCount 8361 15 = 10 ∧ acceleratedOrbit 15 8361 = 15070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8361) = 3 ^ 10 * m + 15070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8361.1, data_15_8361.2]

/-- Complete interval computation for depth 15, residue 8362. -/
theorem bounds_15_8362 : exactInterval 15 8362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8362 : oddCount 8362 15 = 3 ∧ acceleratedOrbit 15 8362 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8362) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8362.1, data_15_8362.2]

/-- Complete interval computation for depth 15, residue 8363. -/
theorem bounds_15_8363 : exactInterval 15 8363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8363 : oddCount 8363 15 = 8 ∧ acceleratedOrbit 15 8363 = 1676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8363) = 3 ^ 8 * m + 1676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8363.1, data_15_8363.2]

/-- Complete interval computation for depth 15, residue 8364. -/
theorem bounds_15_8364 : exactInterval 15 8364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8364 : oddCount 8364 15 = 7 ∧ acceleratedOrbit 15 8364 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8364) = 3 ^ 7 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8364.1, data_15_8364.2]

/-- Complete interval computation for depth 15, residue 8365. -/
theorem bounds_15_8365 : exactInterval 15 8365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8365 : oddCount 8365 15 = 7 ∧ acceleratedOrbit 15 8365 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8365) = 3 ^ 7 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8365.1, data_15_8365.2]

/-- Complete interval computation for depth 15, residue 8366. -/
theorem bounds_15_8366 : exactInterval 15 8366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8366 : oddCount 8366 15 = 7 ∧ acceleratedOrbit 15 8366 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8366) = 3 ^ 7 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8366.1, data_15_8366.2]

/-- Complete interval computation for depth 15, residue 8367. -/
theorem bounds_15_8367 : exactInterval 15 8367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8367 : oddCount 8367 15 = 9 ∧ acceleratedOrbit 15 8367 = 5027 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8367) = 3 ^ 9 * m + 5027 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8367.1, data_15_8367.2]

/-- Complete interval computation for depth 15, residue 8368. -/
theorem bounds_15_8368 : exactInterval 15 8368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8368 : oddCount 8368 15 = 6 ∧ acceleratedOrbit 15 8368 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8368) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8368.1, data_15_8368.2]

/-- Complete interval computation for depth 15, residue 8369. -/
theorem bounds_15_8369 : exactInterval 15 8369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8369 : oddCount 8369 15 = 7 ∧ acceleratedOrbit 15 8369 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8369) = 3 ^ 7 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8369.1, data_15_8369.2]

/-- Complete interval computation for depth 15, residue 8370. -/
theorem bounds_15_8370 : exactInterval 15 8370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8370 : oddCount 8370 15 = 7 ∧ acceleratedOrbit 15 8370 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8370) = 3 ^ 7 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8370.1, data_15_8370.2]

/-- Complete interval computation for depth 15, residue 8371. -/
theorem bounds_15_8371 : exactInterval 15 8371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8371 : oddCount 8371 15 = 7 ∧ acceleratedOrbit 15 8371 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8371) = 3 ^ 7 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8371.1, data_15_8371.2]

/-- Complete interval computation for depth 15, residue 8372. -/
theorem bounds_15_8372 : exactInterval 15 8372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8372 : oddCount 8372 15 = 6 ∧ acceleratedOrbit 15 8372 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8372) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8372.1, data_15_8372.2]

/-- Complete interval computation for depth 15, residue 8373. -/
theorem bounds_15_8373 : exactInterval 15 8373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8373 : oddCount 8373 15 = 6 ∧ acceleratedOrbit 15 8373 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8373) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8373.1, data_15_8373.2]

/-- Complete interval computation for depth 15, residue 8374. -/
theorem bounds_15_8374 : exactInterval 15 8374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8374 : oddCount 8374 15 = 9 ∧ acceleratedOrbit 15 8374 = 5032 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8374) = 3 ^ 9 * m + 5032 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8374.1, data_15_8374.2]

/-- Complete interval computation for depth 15, residue 8375. -/
theorem bounds_15_8375 : exactInterval 15 8375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8375 : oddCount 8375 15 = 9 ∧ acceleratedOrbit 15 8375 = 5032 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8375) = 3 ^ 9 * m + 5032 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8375.1, data_15_8375.2]

/-- Complete interval computation for depth 15, residue 8376. -/
theorem bounds_15_8376 : exactInterval 15 8376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8376 : oddCount 8376 15 = 6 ∧ acceleratedOrbit 15 8376 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8376) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8376.1, data_15_8376.2]

/-- Complete interval computation for depth 15, residue 8377. -/
theorem bounds_15_8377 : exactInterval 15 8377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8377 : oddCount 8377 15 = 9 ∧ acceleratedOrbit 15 8377 = 5035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8377) = 3 ^ 9 * m + 5035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8377.1, data_15_8377.2]

/-- Complete interval computation for depth 15, residue 8378. -/
theorem bounds_15_8378 : exactInterval 15 8378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8378 : oddCount 8378 15 = 6 ∧ acceleratedOrbit 15 8378 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8378) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8378.1, data_15_8378.2]

/-- Complete interval computation for depth 15, residue 8379. -/
theorem bounds_15_8379 : exactInterval 15 8379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8379 : oddCount 8379 15 = 9 ∧ acceleratedOrbit 15 8379 = 5035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8379) = 3 ^ 9 * m + 5035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8379.1, data_15_8379.2]

/-- Complete interval computation for depth 15, residue 8380. -/
theorem bounds_15_8380 : exactInterval 15 8380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8380 : oddCount 8380 15 = 8 ∧ acceleratedOrbit 15 8380 = 1679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8380) = 3 ^ 8 * m + 1679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8380.1, data_15_8380.2]

/-- Complete interval computation for depth 15, residue 8381. -/
theorem bounds_15_8381 : exactInterval 15 8381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8381 : oddCount 8381 15 = 8 ∧ acceleratedOrbit 15 8381 = 1679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8381) = 3 ^ 8 * m + 1679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8381.1, data_15_8381.2]

/-- Complete interval computation for depth 15, residue 8382. -/
theorem bounds_15_8382 : exactInterval 15 8382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8382 : oddCount 8382 15 = 8 ∧ acceleratedOrbit 15 8382 = 1679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8382) = 3 ^ 8 * m + 1679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8382.1, data_15_8382.2]

/-- Complete interval computation for depth 15, residue 8383. -/
theorem bounds_15_8383 : exactInterval 15 8383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8383 : oddCount 8383 15 = 10 ∧ acceleratedOrbit 15 8383 = 15110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8383) = 3 ^ 10 * m + 15110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8383.1, data_15_8383.2]

/-- Complete interval computation for depth 15, residue 8384. -/
theorem bounds_15_8384 : exactInterval 15 8384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8384 : oddCount 8384 15 = 3 ∧ acceleratedOrbit 15 8384 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8384) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8384.1, data_15_8384.2]

/-- Complete interval computation for depth 15, residue 8385. -/
theorem bounds_15_8385 : exactInterval 15 8385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8385 : oddCount 8385 15 = 9 ∧ acceleratedOrbit 15 8385 = 5042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8385) = 3 ^ 9 * m + 5042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8385.1, data_15_8385.2]

/-- Complete interval computation for depth 15, residue 8386. -/
theorem bounds_15_8386 : exactInterval 15 8386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8386 : oddCount 8386 15 = 9 ∧ acceleratedOrbit 15 8386 = 5042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8386) = 3 ^ 9 * m + 5042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8386.1, data_15_8386.2]

/-- Complete interval computation for depth 15, residue 8387. -/
theorem bounds_15_8387 : exactInterval 15 8387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8387 : oddCount 8387 15 = 9 ∧ acceleratedOrbit 15 8387 = 5042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8387) = 3 ^ 9 * m + 5042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8387.1, data_15_8387.2]

end Collatz.Research.PassageAtlas.Batch0256
