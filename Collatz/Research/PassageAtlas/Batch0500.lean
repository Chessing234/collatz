import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0500

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16351. -/
theorem bounds_15_16351 : exactInterval 15 16351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16351 : oddCount 16351 15 = 9 ∧ acceleratedOrbit 15 16351 = 9823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16351) = 3 ^ 9 * m + 9823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16351.1, data_15_16351.2]

/-- Complete interval computation for depth 15, residue 16352. -/
theorem bounds_15_16352 : exactInterval 15 16352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16352 : oddCount 16352 15 = 9 ∧ acceleratedOrbit 15 16352 = 9841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16352) = 3 ^ 9 * m + 9841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16352.1, data_15_16352.2]

/-- Complete interval computation for depth 15, residue 16353. -/
theorem bounds_15_16353 : exactInterval 15 16353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16353 : oddCount 16353 15 = 10 ∧ acceleratedOrbit 15 16353 = 29474 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16353) = 3 ^ 10 * m + 29474 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16353.1, data_15_16353.2]

/-- Complete interval computation for depth 15, residue 16354. -/
theorem bounds_15_16354 : exactInterval 15 16354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16354 : oddCount 16354 15 = 8 ∧ acceleratedOrbit 15 16354 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16354) = 3 ^ 8 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16354.1, data_15_16354.2]

/-- Complete interval computation for depth 15, residue 16355. -/
theorem bounds_15_16355 : exactInterval 15 16355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16355 : oddCount 16355 15 = 8 ∧ acceleratedOrbit 15 16355 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16355) = 3 ^ 8 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16355.1, data_15_16355.2]

/-- Complete interval computation for depth 15, residue 16356. -/
theorem bounds_15_16356 : exactInterval 15 16356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16356 : oddCount 16356 15 = 8 ∧ acceleratedOrbit 15 16356 = 3277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16356) = 3 ^ 8 * m + 3277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16356.1, data_15_16356.2]

/-- Complete interval computation for depth 15, residue 16357. -/
theorem bounds_15_16357 : exactInterval 15 16357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16357 : oddCount 16357 15 = 8 ∧ acceleratedOrbit 15 16357 = 3277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16357) = 3 ^ 8 * m + 3277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16357.1, data_15_16357.2]

/-- Complete interval computation for depth 15, residue 16358. -/
theorem bounds_15_16358 : exactInterval 15 16358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16358 : oddCount 16358 15 = 8 ∧ acceleratedOrbit 15 16358 = 3277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16358) = 3 ^ 8 * m + 3277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16358.1, data_15_16358.2]

/-- Complete interval computation for depth 15, residue 16359. -/
theorem bounds_15_16359 : exactInterval 15 16359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16359 : oddCount 16359 15 = 11 ∧ acceleratedOrbit 15 16359 = 88451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16359) = 3 ^ 11 * m + 88451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16359.1, data_15_16359.2]

/-- Complete interval computation for depth 15, residue 16360. -/
theorem bounds_15_16360 : exactInterval 15 16360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16360 : oddCount 16360 15 = 9 ∧ acceleratedOrbit 15 16360 = 9841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16360) = 3 ^ 9 * m + 9841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16360.1, data_15_16360.2]

/-- Complete interval computation for depth 15, residue 16361. -/
theorem bounds_15_16361 : exactInterval 15 16361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16361 : oddCount 16361 15 = 9 ∧ acceleratedOrbit 15 16361 = 9829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16361) = 3 ^ 9 * m + 9829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16361.1, data_15_16361.2]

/-- Complete interval computation for depth 15, residue 16362. -/
theorem bounds_15_16362 : exactInterval 15 16362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16362 : oddCount 16362 15 = 9 ∧ acceleratedOrbit 15 16362 = 9841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16362) = 3 ^ 9 * m + 9841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16362.1, data_15_16362.2]

/-- Complete interval computation for depth 15, residue 16363. -/
theorem bounds_15_16363 : exactInterval 15 16363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16363 : oddCount 16363 15 = 11 ∧ acceleratedOrbit 15 16363 = 88472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16363) = 3 ^ 11 * m + 88472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16363.1, data_15_16363.2]

/-- Complete interval computation for depth 15, residue 16364. -/
theorem bounds_15_16364 : exactInterval 15 16364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16364 : oddCount 16364 15 = 8 ∧ acceleratedOrbit 15 16364 = 3278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16364) = 3 ^ 8 * m + 3278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16364.1, data_15_16364.2]

/-- Complete interval computation for depth 15, residue 16365. -/
theorem bounds_15_16365 : exactInterval 15 16365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16365 : oddCount 16365 15 = 8 ∧ acceleratedOrbit 15 16365 = 3278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16365) = 3 ^ 8 * m + 3278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16365.1, data_15_16365.2]

/-- Complete interval computation for depth 15, residue 16366. -/
theorem bounds_15_16366 : exactInterval 15 16366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16366 : oddCount 16366 15 = 8 ∧ acceleratedOrbit 15 16366 = 3278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16366) = 3 ^ 8 * m + 3278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16366.1, data_15_16366.2]

/-- Complete interval computation for depth 15, residue 16367. -/
theorem bounds_15_16367 : exactInterval 15 16367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16367 : oddCount 16367 15 = 10 ∧ acceleratedOrbit 15 16367 = 29497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16367) = 3 ^ 10 * m + 29497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16367.1, data_15_16367.2]

/-- Complete interval computation for depth 15, residue 16368. -/
theorem bounds_15_16368 : exactInterval 15 16368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16368 : oddCount 16368 15 = 10 ∧ acceleratedOrbit 15 16368 = 29524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16368) = 3 ^ 10 * m + 29524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16368.1, data_15_16368.2]

/-- Complete interval computation for depth 15, residue 16369. -/
theorem bounds_15_16369 : exactInterval 15 16369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16369 : oddCount 16369 15 = 9 ∧ acceleratedOrbit 15 16369 = 9841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16369) = 3 ^ 9 * m + 9841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16369.1, data_15_16369.2]

/-- Complete interval computation for depth 15, residue 16370. -/
theorem bounds_15_16370 : exactInterval 15 16370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16370 : oddCount 16370 15 = 10 ∧ acceleratedOrbit 15 16370 = 29510 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16370) = 3 ^ 10 * m + 29510 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16370.1, data_15_16370.2]

/-- Complete interval computation for depth 15, residue 16371. -/
theorem bounds_15_16371 : exactInterval 15 16371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16371 : oddCount 16371 15 = 10 ∧ acceleratedOrbit 15 16371 = 29510 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16371) = 3 ^ 10 * m + 29510 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16371.1, data_15_16371.2]

/-- Complete interval computation for depth 15, residue 16372. -/
theorem bounds_15_16372 : exactInterval 15 16372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16372 : oddCount 16372 15 = 10 ∧ acceleratedOrbit 15 16372 = 29524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16372) = 3 ^ 10 * m + 29524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16372.1, data_15_16372.2]

/-- Complete interval computation for depth 15, residue 16373. -/
theorem bounds_15_16373 : exactInterval 15 16373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16373 : oddCount 16373 15 = 10 ∧ acceleratedOrbit 15 16373 = 29524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16373) = 3 ^ 10 * m + 29524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16373.1, data_15_16373.2]

/-- Complete interval computation for depth 15, residue 16374. -/
theorem bounds_15_16374 : exactInterval 15 16374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16374 : oddCount 16374 15 = 9 ∧ acceleratedOrbit 15 16374 = 9838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16374) = 3 ^ 9 * m + 9838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16374.1, data_15_16374.2]

/-- Complete interval computation for depth 15, residue 16375. -/
theorem bounds_15_16375 : exactInterval 15 16375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16375 : oddCount 16375 15 = 9 ∧ acceleratedOrbit 15 16375 = 9838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16375) = 3 ^ 9 * m + 9838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16375.1, data_15_16375.2]

/-- Complete interval computation for depth 15, residue 16376. -/
theorem bounds_15_16376 : exactInterval 15 16376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16376 : oddCount 16376 15 = 11 ∧ acceleratedOrbit 15 16376 = 88573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16376) = 3 ^ 11 * m + 88573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16376.1, data_15_16376.2]

/-- Complete interval computation for depth 15, residue 16377. -/
theorem bounds_15_16377 : exactInterval 15 16377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16377 : oddCount 16377 15 = 9 ∧ acceleratedOrbit 15 16377 = 9839 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16377) = 3 ^ 9 * m + 9839 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16377.1, data_15_16377.2]

/-- Complete interval computation for depth 15, residue 16378. -/
theorem bounds_15_16378 : exactInterval 15 16378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16378 : oddCount 16378 15 = 11 ∧ acceleratedOrbit 15 16378 = 88573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16378) = 3 ^ 11 * m + 88573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16378.1, data_15_16378.2]

/-- Complete interval computation for depth 15, residue 16379. -/
theorem bounds_15_16379 : exactInterval 15 16379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16379 : oddCount 16379 15 = 11 ∧ acceleratedOrbit 15 16379 = 88559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16379) = 3 ^ 11 * m + 88559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16379.1, data_15_16379.2]

/-- Complete interval computation for depth 15, residue 16380. -/
theorem bounds_15_16380 : exactInterval 15 16380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16380 : oddCount 16380 15 = 12 ∧ acceleratedOrbit 15 16380 = 265720 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16380) = 3 ^ 12 * m + 265720 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16380.1, data_15_16380.2]

/-- Complete interval computation for depth 15, residue 16381. -/
theorem bounds_15_16381 : exactInterval 15 16381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16381 : oddCount 16381 15 = 12 ∧ acceleratedOrbit 15 16381 = 265720 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16381) = 3 ^ 12 * m + 265720 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16381.1, data_15_16381.2]

/-- Complete interval computation for depth 15, residue 16382. -/
theorem bounds_15_16382 : exactInterval 15 16382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16382 : oddCount 16382 15 = 13 ∧ acceleratedOrbit 15 16382 = 797161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16382) = 3 ^ 13 * m + 797161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16382.1, data_15_16382.2]

/-- Complete interval computation for depth 15, residue 16383. -/
theorem bounds_15_16383 : exactInterval 15 16383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16383 : oddCount 16383 15 = 14 ∧ acceleratedOrbit 15 16383 = 2391484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16383) = 3 ^ 14 * m + 2391484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16383.1, data_15_16383.2]

end Collatz.Research.PassageAtlas.Batch0500
