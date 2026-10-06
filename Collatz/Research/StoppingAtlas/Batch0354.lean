import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0354

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2350. -/
theorem bounds_12_2350 : exactInterval 12 2350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2350 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2350) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2350 : oddCount 2350 12 = 4 ∧ acceleratedOrbit 12 2350 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2350 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2350) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2350.1, data_12_2350.2]

/-- Complete interval computation for depth 12, residue 2351. -/
theorem bounds_12_2351 : exactInterval 12 2351 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2351 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2351) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2351 : oddCount 2351 12 = 7 ∧ acceleratedOrbit 12 2351 = 1256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2351 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2351) = 3 ^ 7 * m + 1256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2351.1, data_12_2351.2]

/-- Complete interval computation for depth 12, residue 2352. -/
theorem bounds_12_2352 : exactInterval 12 2352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2352 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2352) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2352 : oddCount 2352 12 = 4 ∧ acceleratedOrbit 12 2352 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2352 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2352) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2352.1, data_12_2352.2]

/-- Complete interval computation for depth 12, residue 2353. -/
theorem bounds_12_2353 : exactInterval 12 2353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2353 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2353) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2353 : oddCount 2353 12 = 5 ∧ acceleratedOrbit 12 2353 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2353 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2353) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2353.1, data_12_2353.2]

/-- Complete interval computation for depth 12, residue 2354. -/
theorem bounds_12_2354 : exactInterval 12 2354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2354 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2354) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2354 : oddCount 2354 12 = 5 ∧ acceleratedOrbit 12 2354 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2354 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2354) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2354.1, data_12_2354.2]

/-- Complete interval computation for depth 12, residue 2355. -/
theorem bounds_12_2355 : exactInterval 12 2355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2355 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2355) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2355 : oddCount 2355 12 = 5 ∧ acceleratedOrbit 12 2355 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2355 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2355) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2355.1, data_12_2355.2]

/-- Complete interval computation for depth 12, residue 2356. -/
theorem bounds_12_2356 : exactInterval 12 2356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2356 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2356) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2356 : oddCount 2356 12 = 4 ∧ acceleratedOrbit 12 2356 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2356 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2356) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2356.1, data_12_2356.2]

/-- Complete interval computation for depth 12, residue 2357. -/
theorem bounds_12_2357 : exactInterval 12 2357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2357 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2357) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2357 : oddCount 2357 12 = 4 ∧ acceleratedOrbit 12 2357 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2357 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2357) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2357.1, data_12_2357.2]

/-- Complete interval computation for depth 12, residue 2358. -/
theorem bounds_12_2358 : exactInterval 12 2358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2358 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2358) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2358 : oddCount 2358 12 = 8 ∧ acceleratedOrbit 12 2358 = 3782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2358 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2358) = 3 ^ 8 * m + 3782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2358.1, data_12_2358.2]

/-- Complete interval computation for depth 12, residue 2359. -/
theorem bounds_12_2359 : exactInterval 12 2359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2359 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2359) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2359 : oddCount 2359 12 = 8 ∧ acceleratedOrbit 12 2359 = 3782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2359 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2359) = 3 ^ 8 * m + 3782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2359.1, data_12_2359.2]

/-- Complete interval computation for depth 12, residue 2360. -/
theorem bounds_12_2360 : exactInterval 12 2360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2360 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2360) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2360 : oddCount 2360 12 = 6 ∧ acceleratedOrbit 12 2360 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2360 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2360) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2360.1, data_12_2360.2]

/-- Complete interval computation for depth 12, residue 2361. -/
theorem bounds_12_2361 : exactInterval 12 2361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2361 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2361) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2361 : oddCount 2361 12 = 7 ∧ acceleratedOrbit 12 2361 = 1262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2361 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2361) = 3 ^ 7 * m + 1262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2361.1, data_12_2361.2]

/-- Complete interval computation for depth 12, residue 2362. -/
theorem bounds_12_2362 : exactInterval 12 2362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2362 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2362) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2362 : oddCount 2362 12 = 6 ∧ acceleratedOrbit 12 2362 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2362 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2362) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2362.1, data_12_2362.2]

/-- Complete interval computation for depth 12, residue 2363. -/
theorem bounds_12_2363 : exactInterval 12 2363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2363 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2363) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2363 : oddCount 2363 12 = 6 ∧ acceleratedOrbit 12 2363 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2363 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2363) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2363.1, data_12_2363.2]

/-- Complete interval computation for depth 12, residue 2364. -/
theorem bounds_12_2364 : exactInterval 12 2364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2364 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2364) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2364 : oddCount 2364 12 = 6 ∧ acceleratedOrbit 12 2364 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2364 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2364) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2364.1, data_12_2364.2]

end Collatz.Research.StoppingAtlas.Batch0354
