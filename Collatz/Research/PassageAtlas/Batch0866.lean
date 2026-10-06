import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0866

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28344. -/
theorem bounds_15_28344 : exactInterval 15 28344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28344 : oddCount 28344 15 = 6 ∧ acceleratedOrbit 15 28344 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28344) = 3 ^ 6 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28344.1, data_15_28344.2]

/-- Complete interval computation for depth 15, residue 28345. -/
theorem bounds_15_28345 : exactInterval 15 28345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28345 : oddCount 28345 15 = 9 ∧ acceleratedOrbit 15 28345 = 17030 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28345) = 3 ^ 9 * m + 17030 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28345.1, data_15_28345.2]

/-- Complete interval computation for depth 15, residue 28346. -/
theorem bounds_15_28346 : exactInterval 15 28346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28346 : oddCount 28346 15 = 6 ∧ acceleratedOrbit 15 28346 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28346) = 3 ^ 6 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28346.1, data_15_28346.2]

/-- Complete interval computation for depth 15, residue 28347. -/
theorem bounds_15_28347 : exactInterval 15 28347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28347 : oddCount 28347 15 = 9 ∧ acceleratedOrbit 15 28347 = 17030 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28347) = 3 ^ 9 * m + 17030 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28347.1, data_15_28347.2]

/-- Complete interval computation for depth 15, residue 28348. -/
theorem bounds_15_28348 : exactInterval 15 28348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28348 : oddCount 28348 15 = 6 ∧ acceleratedOrbit 15 28348 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28348) = 3 ^ 6 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28348.1, data_15_28348.2]

/-- Complete interval computation for depth 15, residue 28349. -/
theorem bounds_15_28349 : exactInterval 15 28349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28349 : oddCount 28349 15 = 6 ∧ acceleratedOrbit 15 28349 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28349) = 3 ^ 6 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28349.1, data_15_28349.2]

/-- Complete interval computation for depth 15, residue 28350. -/
theorem bounds_15_28350 : exactInterval 15 28350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28350 : oddCount 28350 15 = 6 ∧ acceleratedOrbit 15 28350 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28350) = 3 ^ 6 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28350.1, data_15_28350.2]

/-- Complete interval computation for depth 15, residue 28351. -/
theorem bounds_15_28351 : exactInterval 15 28351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28351 : oddCount 28351 15 = 10 ∧ acceleratedOrbit 15 28351 = 51092 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28351) = 3 ^ 10 * m + 51092 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28351.1, data_15_28351.2]

/-- Complete interval computation for depth 15, residue 28352. -/
theorem bounds_15_28352 : exactInterval 15 28352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28352 : oddCount 28352 15 = 5 ∧ acceleratedOrbit 15 28352 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28352) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28352.1, data_15_28352.2]

/-- Complete interval computation for depth 15, residue 28353. -/
theorem bounds_15_28353 : exactInterval 15 28353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28353 : oddCount 28353 15 = 6 ∧ acceleratedOrbit 15 28353 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28353) = 3 ^ 6 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28353.1, data_15_28353.2]

/-- Complete interval computation for depth 15, residue 28354. -/
theorem bounds_15_28354 : exactInterval 15 28354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28354 : oddCount 28354 15 = 9 ∧ acceleratedOrbit 15 28354 = 17036 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28354) = 3 ^ 9 * m + 17036 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28354.1, data_15_28354.2]

/-- Complete interval computation for depth 15, residue 28355. -/
theorem bounds_15_28355 : exactInterval 15 28355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28355 : oddCount 28355 15 = 9 ∧ acceleratedOrbit 15 28355 = 17036 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28355) = 3 ^ 9 * m + 17036 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28355.1, data_15_28355.2]

/-- Complete interval computation for depth 15, residue 28356. -/
theorem bounds_15_28356 : exactInterval 15 28356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28356 : oddCount 28356 15 = 5 ∧ acceleratedOrbit 15 28356 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28356) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28356.1, data_15_28356.2]

/-- Complete interval computation for depth 15, residue 28357. -/
theorem bounds_15_28357 : exactInterval 15 28357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28357 : oddCount 28357 15 = 5 ∧ acceleratedOrbit 15 28357 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28357) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28357.1, data_15_28357.2]

/-- Complete interval computation for depth 15, residue 28358. -/
theorem bounds_15_28358 : exactInterval 15 28358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28358 : oddCount 28358 15 = 5 ∧ acceleratedOrbit 15 28358 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28358) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28358.1, data_15_28358.2]

/-- Complete interval computation for depth 15, residue 28359. -/
theorem bounds_15_28359 : exactInterval 15 28359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28359 : oddCount 28359 15 = 6 ∧ acceleratedOrbit 15 28359 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28359) = 3 ^ 6 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28359.1, data_15_28359.2]

/-- Complete interval computation for depth 15, residue 28360. -/
theorem bounds_15_28360 : exactInterval 15 28360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28360 : oddCount 28360 15 = 5 ∧ acceleratedOrbit 15 28360 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28360) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28360.1, data_15_28360.2]

/-- Complete interval computation for depth 15, residue 28361. -/
theorem bounds_15_28361 : exactInterval 15 28361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28361 : oddCount 28361 15 = 8 ∧ acceleratedOrbit 15 28361 = 5680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28361) = 3 ^ 8 * m + 5680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28361.1, data_15_28361.2]

/-- Complete interval computation for depth 15, residue 28362. -/
theorem bounds_15_28362 : exactInterval 15 28362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28362 : oddCount 28362 15 = 5 ∧ acceleratedOrbit 15 28362 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28362) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28362.1, data_15_28362.2]

/-- Complete interval computation for depth 15, residue 28363. -/
theorem bounds_15_28363 : exactInterval 15 28363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28363 : oddCount 28363 15 = 8 ∧ acceleratedOrbit 15 28363 = 5680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28363) = 3 ^ 8 * m + 5680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28363.1, data_15_28363.2]

/-- Complete interval computation for depth 15, residue 28364. -/
theorem bounds_15_28364 : exactInterval 15 28364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28364 : oddCount 28364 15 = 5 ∧ acceleratedOrbit 15 28364 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28364) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28364.1, data_15_28364.2]

/-- Complete interval computation for depth 15, residue 28365. -/
theorem bounds_15_28365 : exactInterval 15 28365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28365 : oddCount 28365 15 = 5 ∧ acceleratedOrbit 15 28365 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28365) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28365.1, data_15_28365.2]

/-- Complete interval computation for depth 15, residue 28366. -/
theorem bounds_15_28366 : exactInterval 15 28366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28366 : oddCount 28366 15 = 10 ∧ acceleratedOrbit 15 28366 = 51121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28366) = 3 ^ 10 * m + 51121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28366.1, data_15_28366.2]

/-- Complete interval computation for depth 15, residue 28367. -/
theorem bounds_15_28367 : exactInterval 15 28367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28367 : oddCount 28367 15 = 10 ∧ acceleratedOrbit 15 28367 = 51121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28367) = 3 ^ 10 * m + 51121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28367.1, data_15_28367.2]

/-- Complete interval computation for depth 15, residue 28368. -/
theorem bounds_15_28368 : exactInterval 15 28368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28368 : oddCount 28368 15 = 5 ∧ acceleratedOrbit 15 28368 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28368) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28368.1, data_15_28368.2]

/-- Complete interval computation for depth 15, residue 28369. -/
theorem bounds_15_28369 : exactInterval 15 28369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28369 : oddCount 28369 15 = 7 ∧ acceleratedOrbit 15 28369 = 1894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28369) = 3 ^ 7 * m + 1894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28369.1, data_15_28369.2]

/-- Complete interval computation for depth 15, residue 28370. -/
theorem bounds_15_28370 : exactInterval 15 28370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28370 : oddCount 28370 15 = 7 ∧ acceleratedOrbit 15 28370 = 1894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28370) = 3 ^ 7 * m + 1894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28370.1, data_15_28370.2]

/-- Complete interval computation for depth 15, residue 28371. -/
theorem bounds_15_28371 : exactInterval 15 28371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28371 : oddCount 28371 15 = 7 ∧ acceleratedOrbit 15 28371 = 1894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28371) = 3 ^ 7 * m + 1894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28371.1, data_15_28371.2]

/-- Complete interval computation for depth 15, residue 28372. -/
theorem bounds_15_28372 : exactInterval 15 28372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28372 : oddCount 28372 15 = 5 ∧ acceleratedOrbit 15 28372 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28372) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28372.1, data_15_28372.2]

/-- Complete interval computation for depth 15, residue 28373. -/
theorem bounds_15_28373 : exactInterval 15 28373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28373 : oddCount 28373 15 = 5 ∧ acceleratedOrbit 15 28373 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28373) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28373.1, data_15_28373.2]

/-- Complete interval computation for depth 15, residue 28374. -/
theorem bounds_15_28374 : exactInterval 15 28374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28374 : oddCount 28374 15 = 8 ∧ acceleratedOrbit 15 28374 = 5683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28374) = 3 ^ 8 * m + 5683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28374.1, data_15_28374.2]

/-- Complete interval computation for depth 15, residue 28375. -/
theorem bounds_15_28375 : exactInterval 15 28375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28375 : oddCount 28375 15 = 8 ∧ acceleratedOrbit 15 28375 = 5683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28375) = 3 ^ 8 * m + 5683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28375.1, data_15_28375.2]

/-- Complete interval computation for depth 15, residue 28376. -/
theorem bounds_15_28376 : exactInterval 15 28376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28376 : oddCount 28376 15 = 6 ∧ acceleratedOrbit 15 28376 = 632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28376) = 3 ^ 6 * m + 632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28376.1, data_15_28376.2]

end Collatz.Research.PassageAtlas.Batch0866
