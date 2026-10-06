import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0439

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14352. -/
theorem bounds_15_14352 : exactInterval 15 14352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14352 : oddCount 14352 15 = 7 ∧ acceleratedOrbit 15 14352 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14352) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14352.1, data_15_14352.2]

/-- Complete interval computation for depth 15, residue 14353. -/
theorem bounds_15_14353 : exactInterval 15 14353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14353 : oddCount 14353 15 = 5 ∧ acceleratedOrbit 15 14353 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14353) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14353.1, data_15_14353.2]

/-- Complete interval computation for depth 15, residue 14354. -/
theorem bounds_15_14354 : exactInterval 15 14354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14354 : oddCount 14354 15 = 9 ∧ acceleratedOrbit 15 14354 = 8626 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14354) = 3 ^ 9 * m + 8626 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14354.1, data_15_14354.2]

/-- Complete interval computation for depth 15, residue 14355. -/
theorem bounds_15_14355 : exactInterval 15 14355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14355 : oddCount 14355 15 = 9 ∧ acceleratedOrbit 15 14355 = 8626 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14355) = 3 ^ 9 * m + 8626 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14355.1, data_15_14355.2]

/-- Complete interval computation for depth 15, residue 14356. -/
theorem bounds_15_14356 : exactInterval 15 14356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14356 : oddCount 14356 15 = 7 ∧ acceleratedOrbit 15 14356 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14356) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14356.1, data_15_14356.2]

/-- Complete interval computation for depth 15, residue 14357. -/
theorem bounds_15_14357 : exactInterval 15 14357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14357 : oddCount 14357 15 = 7 ∧ acceleratedOrbit 15 14357 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14357) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14357.1, data_15_14357.2]

/-- Complete interval computation for depth 15, residue 14358. -/
theorem bounds_15_14358 : exactInterval 15 14358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14358 : oddCount 14358 15 = 5 ∧ acceleratedOrbit 15 14358 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14358) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14358.1, data_15_14358.2]

/-- Complete interval computation for depth 15, residue 14359. -/
theorem bounds_15_14359 : exactInterval 15 14359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14359 : oddCount 14359 15 = 5 ∧ acceleratedOrbit 15 14359 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14359) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14359.1, data_15_14359.2]

/-- Complete interval computation for depth 15, residue 14360. -/
theorem bounds_15_14360 : exactInterval 15 14360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14360 : oddCount 14360 15 = 7 ∧ acceleratedOrbit 15 14360 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14360) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14360.1, data_15_14360.2]

/-- Complete interval computation for depth 15, residue 14361. -/
theorem bounds_15_14361 : exactInterval 15 14361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14361 : oddCount 14361 15 = 9 ∧ acceleratedOrbit 15 14361 = 8630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14361) = 3 ^ 9 * m + 8630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14361.1, data_15_14361.2]

/-- Complete interval computation for depth 15, residue 14362. -/
theorem bounds_15_14362 : exactInterval 15 14362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14362 : oddCount 14362 15 = 7 ∧ acceleratedOrbit 15 14362 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14362) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14362.1, data_15_14362.2]

/-- Complete interval computation for depth 15, residue 14363. -/
theorem bounds_15_14363 : exactInterval 15 14363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14363 : oddCount 14363 15 = 10 ∧ acceleratedOrbit 15 14363 = 25886 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14363) = 3 ^ 10 * m + 25886 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14363.1, data_15_14363.2]

/-- Complete interval computation for depth 15, residue 14364. -/
theorem bounds_15_14364 : exactInterval 15 14364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14364 : oddCount 14364 15 = 8 ∧ acceleratedOrbit 15 14364 = 2879 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14364) = 3 ^ 8 * m + 2879 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14364.1, data_15_14364.2]

/-- Complete interval computation for depth 15, residue 14365. -/
theorem bounds_15_14365 : exactInterval 15 14365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14365 : oddCount 14365 15 = 8 ∧ acceleratedOrbit 15 14365 = 2879 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14365) = 3 ^ 8 * m + 2879 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14365.1, data_15_14365.2]

/-- Complete interval computation for depth 15, residue 14366. -/
theorem bounds_15_14366 : exactInterval 15 14366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14366 : oddCount 14366 15 = 8 ∧ acceleratedOrbit 15 14366 = 2879 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14366) = 3 ^ 8 * m + 2879 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14366.1, data_15_14366.2]

/-- Complete interval computation for depth 15, residue 14367. -/
theorem bounds_15_14367 : exactInterval 15 14367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14367 : oddCount 14367 15 = 11 ∧ acceleratedOrbit 15 14367 = 77678 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14367) = 3 ^ 11 * m + 77678 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14367.1, data_15_14367.2]

/-- Complete interval computation for depth 15, residue 14368. -/
theorem bounds_15_14368 : exactInterval 15 14368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14368 : oddCount 14368 15 = 6 ∧ acceleratedOrbit 15 14368 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14368) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14368.1, data_15_14368.2]

/-- Complete interval computation for depth 15, residue 14369. -/
theorem bounds_15_14369 : exactInterval 15 14369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14369 : oddCount 14369 15 = 8 ∧ acceleratedOrbit 15 14369 = 2879 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14369) = 3 ^ 8 * m + 2879 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14369.1, data_15_14369.2]

/-- Complete interval computation for depth 15, residue 14370. -/
theorem bounds_15_14370 : exactInterval 15 14370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14370 : oddCount 14370 15 = 7 ∧ acceleratedOrbit 15 14370 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14370) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14370.1, data_15_14370.2]

/-- Complete interval computation for depth 15, residue 14371. -/
theorem bounds_15_14371 : exactInterval 15 14371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14371 : oddCount 14371 15 = 7 ∧ acceleratedOrbit 15 14371 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14371) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14371.1, data_15_14371.2]

/-- Complete interval computation for depth 15, residue 14372. -/
theorem bounds_15_14372 : exactInterval 15 14372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14372 : oddCount 14372 15 = 6 ∧ acceleratedOrbit 15 14372 = 320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14372) = 3 ^ 6 * m + 320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14372.1, data_15_14372.2]

/-- Complete interval computation for depth 15, residue 14373. -/
theorem bounds_15_14373 : exactInterval 15 14373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14373 : oddCount 14373 15 = 6 ∧ acceleratedOrbit 15 14373 = 320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14373) = 3 ^ 6 * m + 320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14373.1, data_15_14373.2]

/-- Complete interval computation for depth 15, residue 14374. -/
theorem bounds_15_14374 : exactInterval 15 14374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14374 : oddCount 14374 15 = 6 ∧ acceleratedOrbit 15 14374 = 320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14374) = 3 ^ 6 * m + 320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14374.1, data_15_14374.2]

/-- Complete interval computation for depth 15, residue 14375. -/
theorem bounds_15_14375 : exactInterval 15 14375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14375 : oddCount 14375 15 = 10 ∧ acceleratedOrbit 15 14375 = 25910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14375) = 3 ^ 10 * m + 25910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14375.1, data_15_14375.2]

/-- Complete interval computation for depth 15, residue 14376. -/
theorem bounds_15_14376 : exactInterval 15 14376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14376 : oddCount 14376 15 = 6 ∧ acceleratedOrbit 15 14376 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14376) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14376.1, data_15_14376.2]

/-- Complete interval computation for depth 15, residue 14377. -/
theorem bounds_15_14377 : exactInterval 15 14377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14377 : oddCount 14377 15 = 8 ∧ acceleratedOrbit 15 14377 = 2879 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14377) = 3 ^ 8 * m + 2879 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14377.1, data_15_14377.2]

/-- Complete interval computation for depth 15, residue 14378. -/
theorem bounds_15_14378 : exactInterval 15 14378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14378 : oddCount 14378 15 = 6 ∧ acceleratedOrbit 15 14378 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14378) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14378.1, data_15_14378.2]

/-- Complete interval computation for depth 15, residue 14379. -/
theorem bounds_15_14379 : exactInterval 15 14379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14379 : oddCount 14379 15 = 6 ∧ acceleratedOrbit 15 14379 = 320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14379) = 3 ^ 6 * m + 320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14379.1, data_15_14379.2]

/-- Complete interval computation for depth 15, residue 14380. -/
theorem bounds_15_14380 : exactInterval 15 14380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14380 : oddCount 14380 15 = 7 ∧ acceleratedOrbit 15 14380 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14380) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14380.1, data_15_14380.2]

/-- Complete interval computation for depth 15, residue 14381. -/
theorem bounds_15_14381 : exactInterval 15 14381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14381 : oddCount 14381 15 = 7 ∧ acceleratedOrbit 15 14381 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14381) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14381.1, data_15_14381.2]

/-- Complete interval computation for depth 15, residue 14382. -/
theorem bounds_15_14382 : exactInterval 15 14382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14382 : oddCount 14382 15 = 7 ∧ acceleratedOrbit 15 14382 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14382) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14382.1, data_15_14382.2]

/-- Complete interval computation for depth 15, residue 14383. -/
theorem bounds_15_14383 : exactInterval 15 14383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14383 : oddCount 14383 15 = 10 ∧ acceleratedOrbit 15 14383 = 25922 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14383) = 3 ^ 10 * m + 25922 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14383.1, data_15_14383.2]

/-- Complete interval computation for depth 15, residue 14384. -/
theorem bounds_15_14384 : exactInterval 15 14384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14384 : oddCount 14384 15 = 6 ∧ acceleratedOrbit 15 14384 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14384) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14384.1, data_15_14384.2]

end Collatz.Research.PassageAtlas.Batch0439
