import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0621

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2355. -/
theorem bounds_13_2355 : exactInterval 13 2355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2355 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2355) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2355 : oddCount 2355 13 = 5 ∧ acceleratedOrbit 13 2355 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2355 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2355) = 3 ^ 5 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2355.1, data_13_2355.2]

/-- Complete interval computation for depth 13, residue 2356. -/
theorem bounds_13_2356 : exactInterval 13 2356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2356 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2356) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2356 : oddCount 2356 13 = 5 ∧ acceleratedOrbit 13 2356 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2356 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2356) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2356.1, data_13_2356.2]

/-- Complete interval computation for depth 13, residue 2357. -/
theorem bounds_13_2357 : exactInterval 13 2357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2357 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2357) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2357 : oddCount 2357 13 = 5 ∧ acceleratedOrbit 13 2357 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2357 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2357) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2357.1, data_13_2357.2]

/-- Complete interval computation for depth 13, residue 2358. -/
theorem bounds_13_2358 : exactInterval 13 2358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2358 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2358) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2358 : oddCount 2358 13 = 8 ∧ acceleratedOrbit 13 2358 = 1891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2358 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2358) = 3 ^ 8 * m + 1891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2358.1, data_13_2358.2]

/-- Complete interval computation for depth 13, residue 2359. -/
theorem bounds_13_2359 : exactInterval 13 2359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2359 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2359) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2359 : oddCount 2359 13 = 8 ∧ acceleratedOrbit 13 2359 = 1891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2359 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2359) = 3 ^ 8 * m + 1891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2359.1, data_13_2359.2]

/-- Complete interval computation for depth 13, residue 2360. -/
theorem bounds_13_2360 : exactInterval 13 2360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2360 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2360) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2360 : oddCount 2360 13 = 6 ∧ acceleratedOrbit 13 2360 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2360 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2360) = 3 ^ 6 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2360.1, data_13_2360.2]

/-- Complete interval computation for depth 13, residue 2361. -/
theorem bounds_13_2361 : exactInterval 13 2361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2361 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2361) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2361 : oddCount 2361 13 = 7 ∧ acceleratedOrbit 13 2361 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2361 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2361) = 3 ^ 7 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2361.1, data_13_2361.2]

/-- Complete interval computation for depth 13, residue 2362. -/
theorem bounds_13_2362 : exactInterval 13 2362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2362 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2362) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2362 : oddCount 2362 13 = 6 ∧ acceleratedOrbit 13 2362 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2362 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2362) = 3 ^ 6 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2362.1, data_13_2362.2]

/-- Complete interval computation for depth 13, residue 2363. -/
theorem bounds_13_2363 : exactInterval 13 2363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2363 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2363) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2363 : oddCount 2363 13 = 6 ∧ acceleratedOrbit 13 2363 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2363 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2363) = 3 ^ 6 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2363.1, data_13_2363.2]

/-- Complete interval computation for depth 13, residue 2364. -/
theorem bounds_13_2364 : exactInterval 13 2364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2364 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2364) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2364 : oddCount 2364 13 = 6 ∧ acceleratedOrbit 13 2364 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2364 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2364) = 3 ^ 6 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2364.1, data_13_2364.2]

/-- Complete interval computation for depth 13, residue 2365. -/
theorem bounds_13_2365 : exactInterval 13 2365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2365 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2365) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2365 : oddCount 2365 13 = 6 ∧ acceleratedOrbit 13 2365 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2365 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2365) = 3 ^ 6 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2365.1, data_13_2365.2]

/-- Complete interval computation for depth 13, residue 2366. -/
theorem bounds_13_2366 : exactInterval 13 2366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2366 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2366) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2366 : oddCount 2366 13 = 9 ∧ acceleratedOrbit 13 2366 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2366 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2366) = 3 ^ 9 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2366.1, data_13_2366.2]

/-- Complete interval computation for depth 13, residue 2367. -/
theorem bounds_13_2367 : exactInterval 13 2367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2367 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2367) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2367 : oddCount 2367 13 = 9 ∧ acceleratedOrbit 13 2367 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2367 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2367) = 3 ^ 9 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2367.1, data_13_2367.2]

/-- Complete interval computation for depth 13, residue 2368. -/
theorem bounds_13_2368 : exactInterval 13 2368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2368 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2368) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2368 : oddCount 2368 13 = 4 ∧ acceleratedOrbit 13 2368 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2368 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2368) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2368.1, data_13_2368.2]

/-- Complete interval computation for depth 13, residue 2369. -/
theorem bounds_13_2369 : exactInterval 13 2369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2369 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2369) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2369 : oddCount 2369 13 = 5 ∧ acceleratedOrbit 13 2369 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2369 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2369) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2369.1, data_13_2369.2]

end Collatz.Research.StoppingAtlas.Batch0621
