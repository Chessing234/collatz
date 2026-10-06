import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0355

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2365. -/
theorem bounds_12_2365 : exactInterval 12 2365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2365 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2365) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2365 : oddCount 2365 12 = 6 ∧ acceleratedOrbit 12 2365 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2365 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2365) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2365.1, data_12_2365.2]

/-- Complete interval computation for depth 12, residue 2366. -/
theorem bounds_12_2366 : exactInterval 12 2366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2366 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2366) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2366 : oddCount 2366 12 = 9 ∧ acceleratedOrbit 12 2366 = 11380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2366 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2366) = 3 ^ 9 * m + 11380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2366.1, data_12_2366.2]

/-- Complete interval computation for depth 12, residue 2367. -/
theorem bounds_12_2367 : exactInterval 12 2367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2367 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2367) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2367 : oddCount 2367 12 = 9 ∧ acceleratedOrbit 12 2367 = 11380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2367 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2367) = 3 ^ 9 * m + 11380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2367.1, data_12_2367.2]

/-- Complete interval computation for depth 12, residue 2368. -/
theorem bounds_12_2368 : exactInterval 12 2368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2368 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2368) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2368 : oddCount 2368 12 = 3 ∧ acceleratedOrbit 12 2368 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2368 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2368) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2368.1, data_12_2368.2]

/-- Complete interval computation for depth 12, residue 2369. -/
theorem bounds_12_2369 : exactInterval 12 2369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2369 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2369) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2369 : oddCount 2369 12 = 4 ∧ acceleratedOrbit 12 2369 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2369 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2369) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2369.1, data_12_2369.2]

/-- Complete interval computation for depth 12, residue 2370. -/
theorem bounds_12_2370 : exactInterval 12 2370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2370 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2370) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2370 : oddCount 2370 12 = 8 ∧ acceleratedOrbit 12 2370 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2370 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2370) = 3 ^ 8 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2370.1, data_12_2370.2]

/-- Complete interval computation for depth 12, residue 2371. -/
theorem bounds_12_2371 : exactInterval 12 2371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2371 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2371) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2371 : oddCount 2371 12 = 8 ∧ acceleratedOrbit 12 2371 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2371 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2371) = 3 ^ 8 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2371.1, data_12_2371.2]

/-- Complete interval computation for depth 12, residue 2372. -/
theorem bounds_12_2372 : exactInterval 12 2372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2372 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2372) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2372 : oddCount 2372 12 = 6 ∧ acceleratedOrbit 12 2372 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2372 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2372) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2372.1, data_12_2372.2]

/-- Complete interval computation for depth 12, residue 2373. -/
theorem bounds_12_2373 : exactInterval 12 2373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2373 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2373) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2373 : oddCount 2373 12 = 6 ∧ acceleratedOrbit 12 2373 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2373 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2373) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2373.1, data_12_2373.2]

/-- Complete interval computation for depth 12, residue 2374. -/
theorem bounds_12_2374 : exactInterval 12 2374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2374 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2374) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2374 : oddCount 2374 12 = 6 ∧ acceleratedOrbit 12 2374 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2374 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2374) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2374.1, data_12_2374.2]

/-- Complete interval computation for depth 12, residue 2375. -/
theorem bounds_12_2375 : exactInterval 12 2375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2375 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2375) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2375 : oddCount 2375 12 = 10 ∧ acceleratedOrbit 12 2375 = 34262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2375 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2375) = 3 ^ 10 * m + 34262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2375.1, data_12_2375.2]

/-- Complete interval computation for depth 12, residue 2376. -/
theorem bounds_12_2376 : exactInterval 12 2376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2376 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2376) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2376 : oddCount 2376 12 = 6 ∧ acceleratedOrbit 12 2376 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2376 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2376) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2376.1, data_12_2376.2]

/-- Complete interval computation for depth 12, residue 2377. -/
theorem bounds_12_2377 : exactInterval 12 2377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2377 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2377) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2377 : oddCount 2377 12 = 7 ∧ acceleratedOrbit 12 2377 = 1271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2377 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2377) = 3 ^ 7 * m + 1271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2377.1, data_12_2377.2]

/-- Complete interval computation for depth 12, residue 2378. -/
theorem bounds_12_2378 : exactInterval 12 2378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2378 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2378) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2378 : oddCount 2378 12 = 6 ∧ acceleratedOrbit 12 2378 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2378 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2378) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2378.1, data_12_2378.2]

/-- Complete interval computation for depth 12, residue 2379. -/
theorem bounds_12_2379 : exactInterval 12 2379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2379 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2379) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2379 : oddCount 2379 12 = 6 ∧ acceleratedOrbit 12 2379 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2379 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2379) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2379.1, data_12_2379.2]

end Collatz.Research.StoppingAtlas.Batch0355
